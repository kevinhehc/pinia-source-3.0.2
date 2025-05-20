import {
  watch,
  computed,
  inject,
  hasInjectionContext,
  getCurrentInstance,
  reactive,
  DebuggerEvent,
  WatchOptions,
  UnwrapRef,
  markRaw,
  isRef,
  isReactive,
  effectScope,
  EffectScope,
  ComputedRef,
  toRaw,
  toRef,
  toRefs,
  Ref,
  ref,
  nextTick,
} from 'vue'
import {
  StateTree,
  SubscriptionCallback,
  _DeepPartial,
  isPlainObject,
  Store,
  _Method,
  DefineStoreOptions,
  StoreDefinition,
  _GettersTree,
  MutationType,
  StoreOnActionListener,
  _ActionsTree,
  SubscriptionCallbackMutation,
  DefineSetupStoreOptions,
  DefineStoreOptionsInPlugin,
  StoreGeneric,
  _StoreWithGetters,
  _StoreWithGetters_Readonly,
  _StoreWithGetters_Writable,
  _ExtractActionsFromSetupStore,
  _ExtractGettersFromSetupStore,
  _ExtractStateFromSetupStore,
  _StoreWithState,
} from './types'
import { setActivePinia, piniaSymbol, Pinia, activePinia } from './rootStore'
import { IS_CLIENT } from './env'
import { patchObject } from './hmr'
import { addSubscription, triggerSubscriptions, noop } from './subscriptions'

// 在不支持 runWithContext() 的平台上，直接执行函数（Polyfill）
// 在新版 Vue + Pinia 中，有时会使用 effectScope.run() 或 withAsyncContext() 来隔离副作用，fallbackRunWithContext 是兜底方案。
const fallbackRunWithContext = (fn: () => unknown) => fn()

// 用于从数组类型中提取元素类型
// 示例：
// type X = _ArrayType<string[]>   // string
// type Y = _ArrayType<number[][]> // number[]
type _ArrayType<AT> = AT extends Array<infer T> ? T : never

/**
 * Marks a function as an action for `$onAction`
 * @internal
 */
// 表示这个函数是一个 action
const ACTION_MARKER = Symbol()
/**
 * Action name symbol. Allows to add a name to an action after defining it
 * @internal
 */
// 存储这个 action 的“名称”（可用于调试、hook 等）
const ACTION_NAME = Symbol()
/**
 * Function type extended with action markers
 * @internal
 */
// 这是一个“增强后的函数类型”，它等价于：
// 和原函数签名完全一样，但多了两个隐藏的 Symbol 属性
// const someAction: MarkedAction<() => void> = () => { ... }
// someAction[ACTION_MARKER] === true
// someAction[ACTION_NAME] === 'someActionName'
// 这使得 Pinia 能在运行时用如下方式检测：
// if (fn[ACTION_MARKER]) {
//   // 这是一个被注册的 action
// }
interface MarkedAction<Fn extends _Method = _Method> {
  (...args: Parameters<Fn>): ReturnType<Fn>
  [ACTION_MARKER]: boolean
  [ACTION_NAME]: string
}

// 用于将一个“补丁对象”合并到一个响应式目标中。它通常出现在 状态持久化（如 SSR hydration）或热更新 的场景中。
// 将 patchToApply 中的数据递归合并到 target 中，支持普通对象、Map、Set，以及嵌套的深层结构，同时保留 Vue 的响应性特性。
function mergeReactiveObjects<
  T extends Record<any, unknown> | Map<unknown, unknown> | Set<unknown>,
>(target: T, patchToApply: _DeepPartial<T>): T {
  // Handle Map instances
  // patchToApply 是一个 _DeepPartial<T>：与 T 结构相同，但所有字段都是可选的、浅/深可省略的副本。
  if (target instanceof Map && patchToApply instanceof Map) {
    // 将 patchToApply 中的键值对合并进 target
    // 不递归，只覆盖一层
    patchToApply.forEach((value, key) => target.set(key, value))
  } else if (target instanceof Set && patchToApply instanceof Set) {
    // Handle Set instances
    // 向 target 添加所有来自 patchToApply 的元素（保持唯一性）
    patchToApply.forEach(target.add, target)
  }

  // no need to go through symbols because they cannot be serialized anyway
  // 处理普通对象（核心）
  for (const key in patchToApply) {
    if (!patchToApply.hasOwnProperty(key)) continue
    const subPatch = patchToApply[key]
    const targetValue = target[key]
    if (
      // 检查是否是嵌套的对象并递归合并：
      isPlainObject(targetValue) &&
      isPlainObject(subPatch) &&
      target.hasOwnProperty(key) &&
      !isRef(subPatch) &&
      !isReactive(subPatch)
    ) {
      // NOTE: here I wanted to warn about inconsistent types but it's not possible because in setup stores one might
      // start the value of a property as a certain type e.g. a Map, and then for some reason, during SSR, change that
      // to `undefined`. When trying to hydrate, we want to override the Map with `undefined`.
      // 递归合并对象（而不是直接替换）
      // 排除：
      // ref（避免破坏响应式引用）
      // reactive（避免 merge 两个响应式代理）
      target[key] = mergeReactiveObjects(targetValue, subPatch)
    } else {
      // @ts-expect-error: subPatch is a valid value
      // 否则直接覆盖：
      // 注意：有 @ts-expect-error 是因为 TS 无法准确推断类型，但这在运行时是安全的。
      target[key] = subPatch
    }
  }

  return target
}

// 创建一个全局唯一的 Symbol 作为对象的隐藏标志属性，用来标记该对象不应被 hydrate。
// 开发模式下会带有描述名称，方便调试。
// 生产模式下是匿名 symbol。
const skipHydrateSymbol = __DEV__
  ? Symbol('pinia:skipHydration')
  : /* istanbul ignore next */ Symbol()

/**
 * Tells Pinia to skip the hydration process of a given object. This is useful in setup stores (only) when you return a
 * stateful object in the store but it isn't really state. e.g. returning a router instance in a setup store.
 *
 * @param obj - target object
 * @returns obj
 */
// 给目标对象加上一个不可枚举的 Symbol 属性，告诉 Pinia：“别对这个对象做 hydration 操作”。
// 它不会影响对象的结构或内容，但通过 Symbol 打标。
// 举例
// const router = useRouter()
// const store = defineStore('x', () => {
//   return {
//     router: skipHydrate(router) // pinia 知道不要尝试替换 router
//   }
// })
export function skipHydrate<T = any>(obj: T): T {
  return Object.defineProperty(obj, skipHydrateSymbol, {})
}

/**
 * Returns whether a value should be hydrated
 *
 * @param obj - target variable
 * @returns true if `obj` should be hydrated
 */
// 用于判断对象是否应该被 hydration。
// 逻辑说明：
// 如果不是一个“普通对象” → 不做 hydration（例如是函数、class 实例、数组等）
// 如果对象上有 skipHydrateSymbol → 也不做 hydration
// 所以只有“普通对象 且 未打跳过标记”才会被 hydrate。
export function shouldHydrate(obj: any) {
  return (
    !isPlainObject(obj) ||
    !Object.prototype.hasOwnProperty.call(obj, skipHydrateSymbol)
  )
}

const { assign } = Object

// 判断一个值是否是 computed() 创建的计算属性。
// 原理：
// 所有 computed 是 ref，但带有 .effect 属性（内部 effect runner）
// 这在 hydration 时也有帮助，因为 Pinia 不应修改 computed 的值。
function isComputed<T>(value: ComputedRef<T> | unknown): value is ComputedRef<T>
function isComputed(o: any): o is ComputedRef {
  return !!(isRef(o) && (o as any).effect)
}

// 用于创建基于传统 options API 写法的 store（相比之下，setup() 写法是另一种模式）。
function createOptionsStore<
  Id extends string,
  S extends StateTree,
  G extends _GettersTree<S>,
  A extends _ActionsTree,
>(
  id: Id,
  options: DefineStoreOptions<Id, S, G, A>,
  pinia: Pinia,
  hot?: boolean
): Store<Id, S, G, A> {
  // 解构用户配置
  // const { state, actions, getters } = options
  // 这是用户通过 defineStore(...) 提供的：
  // defineStore({
  //   id: 'cart',
  //   state: () => ({ items: [] }),
  //   getters: { ... },
  //   actions: { ... }
  // })
  const { state, actions, getters } = options

  // 初始状态（SSR 或 HMR）
  // 查看 Pinia 根状态中是否已有这个 store 的数据（例如 SSR preload 或热更新场景）
  const initialState: StateTree | undefined = pinia.state.value[id]

  let store: Store<Id, S, G, A>

  //  函数核心：生成 store 内容
  // 这是构建 store 实例内部数据的核心逻辑。
  function setup() {
    // 初始化状态（非 HMR / 非开发模式）
    // 如果是第一次初始化，则生成一份 state

    // 存进全局的 pinia.state.value
    if (!initialState && (!__DEV__ || !hot)) {
      /* istanbul ignore if */
      pinia.state.value[id] = state ? state() : {}
    }

    // avoid creating a state in pinia.state.value
    // 如果是开发环境的热更新（hot reload）
    // 使用 ref() + toRefs() 保证响应性解构。
    // HMR 时使用新的 state，而不是复用旧的全局状态。
    const localState =
      __DEV__ && hot
        ? // use ref() to unwrap refs inside state TODO: check if this is still necessary
          toRefs(ref(state ? state() : {}).value)
        : toRefs(pinia.state.value[id])

    // 构建最终的 store 对象
    // 这里是关键点：
    // state: 用 toRefs 包裹，每个字段都是响应式 ref
    // actions: 直接挂到 store 上
    // getters: 被转成 computed()，同时用 markRaw 避免递归代理
    return assign(
      localState,
      actions,
      Object.keys(getters || {}).reduce(
        (computedGetters, name) => {
          if (__DEV__ && name in localState) {
            // Pinia 禁止 getter 和 state 命名重复，避免访问时产生歧义。
            console.warn(
              `[🍍]: A getter cannot have the same name as another state property. Rename one of them. Found with "${name}" in store "${id}".`
            )
          }

          // Getter 实现细节
          // setActivePinia() 设置当前上下文（支持 useStore() 等调用）
          // getter.call(store, store)：
          // 第一个参数是 this（模拟）
          // 第二个参数是 store 本身，用于访问其他 state/getters/actions
          computedGetters[name] = markRaw(
            computed(() => {
              setActivePinia(pinia)
              // it was created just before
              const store = pinia._s.get(id)!

              // allow cross using stores

              // @ts-expect-error
              // return getters![name].call(context, context)
              // TODO: avoid reading the getter while assigning with a global variable
              return getters![name].call(store, store)
            })
          )
          return computedGetters
        },
        {} as Record<string, ComputedRef>
      )
    )
  }

  store = createSetupStore(id, setup, options, pinia, hot, true)

  return store as any
}

// 构建 setup() 模式的 store 实例的核心工厂函数。这段代码在用户首次调用 useStore() 且使用了 setup API 时执行。
// 执行用户定义的 setup() 函数，构造一个完整的 Pinia store 实例，包括：
// 响应式状态（state）
// 动作（actions）
// 计算属性（getters）
// 内部 API（如 $patch, $subscribe, $reset, $dispose）
// 插件支持
// 热更新支持
function createSetupStore<
  Id extends string,
  SS extends Record<any, unknown>,
  S extends StateTree,
  G extends Record<string, _Method>,
  A extends _ActionsTree,
>(
  $id: Id,
  setup: (helpers: SetupStoreHelpers) => SS,
  options:
    | DefineSetupStoreOptions<Id, S, G, A>
    | DefineStoreOptions<Id, S, G, A> = {},
  pinia: Pinia,
  hot?: boolean,
  isOptionsStore?: boolean
): Store<Id, S, G, A> {
  // 1. 准备响应式作用域（EffectScope）
  // 稍后会执行：
  // scope = effectScope()
  // scope.run(() => setup(...))
  // 这个作用域会管理 store 中的所有响应式依赖（方便后续停止、清理、热更新等）
  let scope!: EffectScope

  // 2. 构造插件系统可用的 options 对象
  // 把原始 options 包装为插件能识别的结构（总是包含 actions 字段）
  // 供后续插件调用时使用（如 pinia.use(plugin)）
  const optionsForPlugin: DefineStoreOptionsInPlugin<Id, S, G, A> = assign(
    { actions: {} as A },
    options
  )

  /* istanbul ignore if */
  // 3. 校验 Pinia 实例是否有效
  // _e 是一个 EffectScope
  // 如果整个 Pinia 实例被销毁（如在测试或热替换后），禁止继续构造 store
  if (__DEV__ && !pinia._e.active) {
    throw new Error('Pinia destroyed')
  }

  // watcher options for $subscribe
  // 4. 配置 $subscribe 时的 watcher 选项
  // Pinia 的 $subscribe() 底层基于 watch()，这里预设了选项：
  // 深度监听
  // 并在开发模式中提供调试 onTrigger
  const $subscribeOptions: WatchOptions = { deep: true }
  /* istanbul ignore else */
  if (__DEV__) {
    // onTrigger 的作用（仅开发模式）
    $subscribeOptions.onTrigger = (event) => {
      // onTrigger 用于 Vue DevTools 调试时记录状态变化事件
      // isListening 是 devtools 的一个控制变量（是否启用追踪）
      // debuggerEvents 会收集这些事件，供调试器展示
      /* istanbul ignore else */
      if (isListening) {
        debuggerEvents = event
        // avoid triggering this while the store is being built and the state is being set in pinia
      } else if (isListening == false && !store._hotUpdating) {
        // let patch send all the events together later
        /* istanbul ignore else */
        if (Array.isArray(debuggerEvents)) {
          debuggerEvents.push(event)
        } else {
          console.error(
            '🍍 debuggerEvents should be an array. This is most likely an internal Pinia bug.'
          )
        }
      }
    }
  }

  // internal state
  // let isListening: boolean          // 是否允许触发订阅回调（异步启用）
  // let isSyncListening: boolean      // 是否同步启用订阅监听
  // let subscriptions = []            // 订阅 store 改变的回调
  // let actionSubscriptions = []      // 订阅 action 调用的回调
  // let debuggerEvents                // devtools 使用的事件记录
  let isListening: boolean // set to true at the end
  let isSyncListening: boolean // set to true at the end
  let subscriptions: SubscriptionCallback<S>[] = []
  let actionSubscriptions: StoreOnActionListener<Id, S, G, A>[] = []
  let debuggerEvents: DebuggerEvent[] | DebuggerEvent
  // 初始 state
  const initialState = pinia.state.value[$id] as UnwrapRef<S> | undefined

  // avoid setting the state for option stores if it is set
  // by the setup
  // 如果是 setup store 且还没初始化，则初始化空对象
  // 这一步是在 setup 模式下的初始化防卫性处理。
  if (!isOptionsStore && !initialState && (!__DEV__ || !hot)) {
    /* istanbul ignore if */
    pinia.state.value[$id] = {}
  }

  // hotState 是给 HMR 用的临时状态包裹
  // 它用于记录热重载时替换的字段（仅用于开发环境），不是你写的 state。
  const hotState = ref({} as S)

  // avoid triggering too many listeners
  // https://github.com/vuejs/pinia/issues/1129
  let activeListener: Symbol | undefined
  // 函数签名重载
  // 支持：
  // 函数式批量修改
  // 对象式局部修改
  function $patch(stateMutation: (state: UnwrapRef<S>) => void): void
  function $patch(partialState: _DeepPartial<UnwrapRef<S>>): void
  function $patch(
    partialStateOrMutator:
      | _DeepPartial<UnwrapRef<S>>
      | ((state: UnwrapRef<S>) => void)
  ): void {
    let subscriptionMutation: SubscriptionCallbackMutation<S>
    // 先关闭监听器，避免监听器在 patch 过程中被错误触发。
    isListening = isSyncListening = false
    // reset the debugger events since patches are sync
    /* istanbul ignore else */
    if (__DEV__) {
      //  开发模式下：清空 devtools 的事件记录
      debuggerEvents = []
    }
    //  分支 1：函数式修改
    if (typeof partialStateOrMutator === 'function') {
      // 直接执行回调函数，修改 state
      // 构造订阅事件 payload
      partialStateOrMutator(pinia.state.value[$id] as UnwrapRef<S>)
      subscriptionMutation = {
        type: MutationType.patchFunction,
        storeId: $id,
        events: debuggerEvents as DebuggerEvent[],
      }
    } else {
      //  分支 2：对象合并修改
      // 使用 mergeReactiveObjects() 工具函数，递归合并对象。
      mergeReactiveObjects(pinia.state.value[$id], partialStateOrMutator)
      subscriptionMutation = {
        type: MutationType.patchObject,
        payload: partialStateOrMutator,
        storeId: $id,
        events: debuggerEvents as DebuggerEvent[],
      }
    }
    // 重新启用监听
    // 这里使用了防抖技术，确保只在下一个事件循环恢复监听器
    // 避免嵌套 patch 时提前触发监听
    const myListenerId = (activeListener = Symbol())
    nextTick().then(() => {
      if (activeListener === myListenerId) {
        isListening = true
      }
    })
    isSyncListening = true
    // because we paused the watcher, we need to manually call the subscriptions
    // 触发手动订阅回调
    // 即便关闭了监听器（Watcher 被暂停），也手动触发订阅器通知变化。
    triggerSubscriptions(
      subscriptions,
      subscriptionMutation,
      pinia.state.value[$id] as UnwrapRef<S>
    )
  }

  // 重置 store 的 state 为初始值（仅限 options store）
  // 1、对象 store 支持 reset：
  // 会重新调用用户提供的 state() 函数获取初始值
  // 使用 $patch() 批量重置 state（确保一次性触发订阅）
  // 2、setup store 不支持 reset：
  // 因为 setup 模式的 state 是自由写的，没有标准来源
  // 只能手动自己实现一个类似功能（推荐自定义 action）
  const $reset = isOptionsStore
    ? function $reset(this: _StoreWithState<Id, S, G, A>) {
        const { state } = options as DefineStoreOptions<Id, S, G, A>
        const newState: _DeepPartial<UnwrapRef<S>> = state ? state() : {}
        // we use a patch to group all changes into one single subscription
        this.$patch(($state) => {
          // @ts-expect-error: FIXME: shouldn't error?
          assign($state, newState)
        })
      }
    : /* istanbul ignore next */
      __DEV__
      ? () => {
          throw new Error(
            `🍍: Store "${$id}" is built using the setup syntax and does not implement $reset().`
          )
        }
      : noop

  // 清理 store：停止响应式作用域、清除订阅、移除缓存
  // scope.stop()：停止所有响应式依赖（ref, computed, watch 等）
  // 清空订阅列表
  // 将该 store 从 pinia._s 缓存中删除（未来调用会重新构造）
  // 常见于 SSR 回收、测试 teardown、热更新（HMR）等场景。
  function $dispose() {
    scope.stop()
    subscriptions = []
    actionSubscriptions = []
    pinia._s.delete($id)
  }

  /**
   * Helper that wraps function so it can be tracked with $onAction
   * @param fn - action to wrap
   * @param name - name of the action
   */
  // 包装 action 以支持 $onAction 监听（订阅生命周期）
  // 如果该函数已被包装过（带有 ACTION_MARKER），只设置名称，直接返回。
  //
  // 否则，返回一个 新包装的函数，在内部加入生命周期监听：
  const action = <Fn extends _Method>(fn: Fn, name: string = ''): Fn => {
    if (ACTION_MARKER in fn) {
      // we ensure the name is set from the returned function
      ;(fn as unknown as MarkedAction<Fn>)[ACTION_NAME] = name
      return fn
    }

    const wrappedAction = function (this: any) {
      setActivePinia(pinia)
      const args = Array.from(arguments)

      const afterCallbackList: Array<(resolvedReturn: any) => any> = []
      const onErrorCallbackList: Array<(error: unknown) => unknown> = []
      function after(callback: _ArrayType<typeof afterCallbackList>) {
        afterCallbackList.push(callback)
      }
      function onError(callback: _ArrayType<typeof onErrorCallbackList>) {
        onErrorCallbackList.push(callback)
      }

      // @ts-expect-error
      triggerSubscriptions(actionSubscriptions, {
        args,
        name: wrappedAction[ACTION_NAME],
        store,
        after,
        onError,
      })

      let ret: unknown
      try {
        ret = fn.apply(this && this.$id === $id ? this : store, args)
        // handle sync errors
      } catch (error) {
        triggerSubscriptions(onErrorCallbackList, error)
        throw error
      }

      if (ret instanceof Promise) {
        return ret
          .then((value) => {
            triggerSubscriptions(afterCallbackList, value)
            return value
          })
          .catch((error) => {
            triggerSubscriptions(onErrorCallbackList, error)
            return Promise.reject(error)
          })
      }

      // trigger after callbacks
      triggerSubscriptions(afterCallbackList, ret)
      return ret
    } as MarkedAction<Fn>

    wrappedAction[ACTION_MARKER] = true
    wrappedAction[ACTION_NAME] = name // will be set later

    // @ts-expect-error: we are intentionally limiting the returned type to just Fn
    // because all the added properties are internals that are exposed through `$onAction()` only
    return wrappedAction
  }

  // 1. _hmrPayload：热更新辅助信息对象
  // 给 devtools 和 HMR 使用的结构
  // 在开发模式下注册在最终 store 上
  // 会被 devtools 插件读取和操作，用于保留状态
  const _hmrPayload = /*#__PURE__*/ markRaw({
    actions: {} as Record<string, any>,
    getters: {} as Record<string, Ref>,
    state: [] as string[],
    hotState,
  })

  //  _p: pinia,                     // Pinia 实例
  //   $id,                           // Store ID
  //   $onAction,                     // Action 生命周期订阅
  //   $patch,                        // 状态修改器
  //   $reset,                        // 状态重置（options store 才有）
  //   $subscribe(callback, options) // 状态订阅
  //   $dispose                      // 销毁
  const partialStore = {
    _p: pinia,
    // _s: scope,
    $id,
    $onAction: addSubscription.bind(null, actionSubscriptions),
    $patch,
    $reset,
    $subscribe(callback, options = {}) {
      const removeSubscription = addSubscription(
        subscriptions,
        callback,
        options.detached,
        () => stopWatcher()
      )
      const stopWatcher = scope.run(() =>
        watch(
          () => pinia.state.value[$id] as UnwrapRef<S>,
          (state) => {
            if (options.flush === 'sync' ? isSyncListening : isListening) {
              callback(
                {
                  storeId: $id,
                  type: MutationType.direct,
                  events: debuggerEvents as DebuggerEvent,
                },
                state
              )
            }
          },
          assign({}, $subscribeOptions, options)
        )
      )!

      return removeSubscription
    },
    $dispose,
  } as _StoreWithState<Id, S, G, A>

  // 构建最终 store 对象（响应式）
  // 开发环境下额外加入：
  // _hmrPayload: HMR 支持
  // _customProperties: 供 devtools 添加自定义属性时使用
  // 然后整个 store 对象通过 reactive() 包装，成为响应式对象。
  const store: Store<Id, S, G, A> = reactive(
    __DEV__ || (__USE_DEVTOOLS__ && IS_CLIENT)
      ? assign(
          {
            _hmrPayload,
            _customProperties: markRaw(new Set<string>()), // devtools custom properties
          },
          partialStore
          // must be added later
          // setupStore
        )
      : partialStore
  ) as unknown as Store<Id, S, G, A>

  // store the partial store now so the setup of stores can instantiate each other before they are finished without
  // creating infinite loops.
  // 预注册 store —— 提前注入到 pinia 中
  pinia._s.set($id, store as Store)

  // 获取 runWithContext 执行上下文封装函数
  // 有些环境支持高级运行上下文追踪（如 devtools）
  // 否则退回到简单的 fallbackRunWithContext = fn => fn()
  const runWithContext =
    (pinia._a && pinia._a.runWithContext) || fallbackRunWithContext

  // TODO: idea create skipSerialize that marks properties as non serializable and they are skipped
  // 运行用户的 setup() 并获取返回值
  const setupStore = runWithContext(() =>
    pinia._e.run(() => (scope = effectScope()).run(() => setup({ action }))!)
  )!

  // 创建 Vue 的 effectScope()，捕获 ref/computed/watch 等依赖
  // 执行用户的 setup() 函数，注入 action 包装器
  // 最终得到的 setupStore 是类似这样的对象：
  // {
  //   count: ref(0),
  //   double: computed(() => count.value * 2),
  //   increment: () => { ... }
  // }

  // overwrite existing actions to support $onAction
  // 遍历 setupStore 的每一个字段，并根据其类型（ref、reactive、computed、function）执行不同的初始化策略。
  for (const key in setupStore) {
    const prop = setupStore[key]

    //  1. 处理响应式 state
    if ((isRef(prop) && !isComputed(prop)) || isReactive(prop)) {
      // mark it as a piece of state to be serialized
      if (__DEV__ && hot) {
        hotState.value[key] = toRef(setupStore, key)
        // createOptionStore directly sets the state in pinia.state.value so we
        // can just skip that
      } else if (!isOptionsStore) {
        //  状态初始化与 hydration
        // in setup stores we must hydrate the state and sync pinia state tree with the refs the user just created
        if (initialState && shouldHydrate(prop)) {
          // 如果是 SSR hydration，就把初始值同步进 ref/reactive
          if (isRef(prop)) {
            // 只有 setup store 才需要手动把 state 注册到 pinia.state，option store 会自动处理。
            // 同步到 pinia.state 全局状态树中
            prop.value = initialState[key as keyof UnwrapRef<S>]
          } else {
            // probably a reactive object, lets recursively assign
            // @ts-expect-error: prop is unknown
            mergeReactiveObjects(prop, initialState[key])
          }
        }
        // transfer the ref to the pinia state to keep everything in sync
        pinia.state.value[$id][key] = prop
      }

      /* istanbul ignore else */
      if (__DEV__) {
        // HMR 支持
        // 为热更新记录 ref 到 hotState，用于后续恢复。
        _hmrPayload.state.push(key)
      }
      // action
    } else if (typeof prop === 'function') {
      //  2. 处理函数 —— action
      // 自动识别 function 为 action：

      // 包装 action 以支持 $onAction
      // 非热更新场景使用 action() 封装函数，提供：
      // 生命周期钩子：after()、onError()
      // 支持 devtools 追踪
      const actionValue = __DEV__ && hot ? prop : action(prop as _Method, key)
      // this a hot module replacement store because the hotUpdate method needs
      // to do it with the right context
      // @ts-expect-error
      setupStore[key] = actionValue

      /* istanbul ignore else */
      if (__DEV__) {
        _hmrPayload.actions[key] = prop
      }

      // list actions so they can be used in plugins
      // @ts-expect-error
      optionsForPlugin.actions[key] = prop
    } else if (__DEV__) {
      // add getters for devtools
      // 3. 处理 computed —— 作为 getter
      if (isComputed(prop)) {
        _hmrPayload.getters[key] = isOptionsStore
          ? // @ts-expect-error
            options.getters[key]
          : prop
        if (IS_CLIENT) {
          const getters: string[] =
            (setupStore._getters as string[]) ||
            // @ts-expect-error: same
            ((setupStore._getters = markRaw([])) as string[])
          getters.push(key)
        }
      }
    }
  }

  // add the state, getters, and action properties
  /* istanbul ignore if */
  // 添加用户返回的属性到 store 实例
  // setup() 返回的所有属性添加到 store 上。
  // 第二次 assign(toRaw(store)) 是为 storeToRefs() 能正常工作（解开 reactive() 包裹的代理，支持 ref 提取）。
  assign(store, setupStore)
  // allows retrieving reactive objects with `storeToRefs()`. Must be called after assigning to the reactive object.
  // Make `storeToRefs()` work with `reactive()` #799
  assign(toRaw(store), setupStore)

  // use this instead of a computed with setter to be able to create it anywhere
  // without linking the computed lifespan to wherever the store is first
  // created.
  // 设置 $state 属性的 getter/setter
  Object.defineProperty(store, '$state', {
    get: () => (__DEV__ && hot ? hotState.value : pinia.state.value[$id]),
    set: (state) => {
      // $state 提供访问 store 根状态的能力，通常用于：
      // store.$state.name = 'newName'
      // 赋值时，实际内部调用 $patch()，确保触发订阅逻辑。
      // HMR 模式下禁止直接修改 hotState.value。
      /* istanbul ignore if */
      if (__DEV__ && hot) {
        throw new Error('cannot set hotState')
      }
      $patch(($state) => {
        // @ts-expect-error: FIXME: shouldn't error?
        assign($state, state)
      })
    },
  })

  // add the hotUpdate before plugins to allow them to override it
  /* istanbul ignore else */
  if (__DEV__) {
    // 添加 _hotUpdate()：支持 HMR（热模块替换）
    // 这个函数允许热替换 store 的内容，包括：
    // 🔁 替换 state：
    // newStore.$state[stateKey] = oldStateSource
    // 如果新旧 state 都是对象 → 使用 patchObject 递归合并
    // 否则直接替换 ref
    // 🔁 替换 action：
    // store[actionName] = action(actionFn, actionName)
    // 对新的 action 使用 action() 包装后替换旧的
    // 🔁 替换 getter：
    // store[getterName] = computed(() => getter.call(store, store))
    // 对于 options store，要重新构造 computed
    // setup store 直接复用 getter（getter 本身就是 computed）
    // 🔁 移除旧的：
    // 若某些旧的 state/getter/action 不再存在于新的定义中，则删除之。
    store._hotUpdate = markRaw((newStore) => {
      store._hotUpdating = true
      newStore._hmrPayload.state.forEach((stateKey) => {
        if (stateKey in store.$state) {
          const newStateTarget = newStore.$state[stateKey]
          const oldStateSource = store.$state[stateKey as keyof UnwrapRef<S>]
          if (
            typeof newStateTarget === 'object' &&
            isPlainObject(newStateTarget) &&
            isPlainObject(oldStateSource)
          ) {
            patchObject(newStateTarget, oldStateSource)
          } else {
            // transfer the ref
            newStore.$state[stateKey] = oldStateSource
          }
        }
        // patch direct access properties to allow store.stateProperty to work as
        // store.$state.stateProperty
        // @ts-expect-error: any type
        store[stateKey] = toRef(newStore.$state, stateKey)
      })

      // remove deleted state properties
      Object.keys(store.$state).forEach((stateKey) => {
        if (!(stateKey in newStore.$state)) {
          // @ts-expect-error: noop if doesn't exist
          delete store[stateKey]
        }
      })

      // avoid devtools logging this as a mutation
      isListening = false
      isSyncListening = false
      pinia.state.value[$id] = toRef(newStore._hmrPayload, 'hotState')
      isSyncListening = true
      nextTick().then(() => {
        isListening = true
      })

      for (const actionName in newStore._hmrPayload.actions) {
        const actionFn: _Method = newStore[actionName]

        // @ts-expect-error: actionName is a string
        store[actionName] =
          //
          action(actionFn, actionName)
      }

      // TODO: does this work in both setup and option store?
      for (const getterName in newStore._hmrPayload.getters) {
        const getter: _Method = newStore._hmrPayload.getters[getterName]
        const getterValue = isOptionsStore
          ? // special handling of options api
            computed(() => {
              setActivePinia(pinia)
              return getter.call(store, store)
            })
          : getter

        // @ts-expect-error: getterName is a string
        store[getterName] =
          //
          getterValue
      }

      // remove deleted getters
      Object.keys(store._hmrPayload.getters).forEach((key) => {
        if (!(key in newStore._hmrPayload.getters)) {
          // @ts-expect-error: noop if doesn't exist
          delete store[key]
        }
      })

      // remove old actions
      Object.keys(store._hmrPayload.actions).forEach((key) => {
        if (!(key in newStore._hmrPayload.actions)) {
          // @ts-expect-error: noop if doesn't exist
          delete store[key]
        }
      })

      // update the values used in devtools and to allow deleting new properties later on
      store._hmrPayload = newStore._hmrPayload
      store._getters = newStore._getters
      store._hotUpdating = false
    })
  }

  if (__USE_DEVTOOLS__ && IS_CLIENT) {
    const nonEnumerable = {
      writable: true,
      configurable: true,
      // avoid warning on devtools trying to display this property
      enumerable: false,
    }

    // avoid listing internal properties in devtools
    ;(['_p', '_hmrPayload', '_getters', '_customProperties'] as const).forEach(
      (p) => {
        Object.defineProperty(
          store,
          p,
          assign({ value: store[p] }, nonEnumerable)
        )
      }
    )
  }

  // apply all plugins
  // 插件系统：遍历并调用所有 extender 插件
  pinia._p.forEach((extender) => {
    /* istanbul ignore else */
    // // devtools 模式记录扩展的自定义属性
    if (__USE_DEVTOOLS__ && IS_CLIENT) {
      const extensions = scope.run(() =>
        extender({
          store: store as Store,
          app: pinia._a,
          pinia,
          options: optionsForPlugin,
        })
      )!
      Object.keys(extensions || {}).forEach((key) =>
        store._customProperties.add(key)
      )
      assign(store, extensions)
    } else {
      assign(
        store,
        scope.run(() =>
          extender({
            store: store as Store,
            app: pinia._a,
            pinia,
            options: optionsForPlugin,
          })
        )!
      )
    }
  })

  if (
    __DEV__ &&
    store.$state &&
    typeof store.$state === 'object' &&
    typeof store.$state.constructor === 'function' &&
    !store.$state.constructor.toString().includes('[native code]')
  ) {
    //  警告：state 必须是普通对象
    // Pinia 要求 state() 返回值必须是纯对象，不能是自定义类（否则响应性可能失效，且无法序列化）。这段代码会在你写出如下代码时报错：
    // state: () => new MyClass()
    console.warn(
      `[🍍]: The "state" must be a plain object. It cannot be\n` +
        `\tstate: () => new MyClass()\n` +
        `Found in store "${store.$id}".`
    )
  }

  // only apply hydrate to option stores with an initial state in pinia
  // hydration 生命周期钩子（仅 options store）
  // 可以给 options store 写一个 hydrate() 函数，用于从服务器传来的 initialState 手动合并状态：
  // defineStore({
  //   id: 'user',
  //   state: () => ({ name: '' }),
  //   hydrate(state, initialState) {
  //     Object.assign(state, initialState)
  //   }
  // })
  // 这允许你自定义 hydration 逻辑，比如解包 dates、classes、BigInts 等。
  if (
    initialState &&
    isOptionsStore &&
    (options as DefineStoreOptions<Id, S, G, A>).hydrate
  ) {
    ;(options as DefineStoreOptions<Id, S, G, A>).hydrate!(
      store.$state,
      initialState
    )
  }

  // 最后启用监听，并返回 store 实例
  // 允许后续的状态变更被 $subscribe() 监听器捕捉。
  isListening = true
  isSyncListening = true

  // 最终返回的 store 结构类似：
  // {
  //   $id: 'counter',
  //   $patch,
  //   $subscribe,
  //   $onAction,
  //   $dispose,
  //   count: ref(0),
  //   double: computed(...),
  //   increment: () => { ... },
  //   hello: () => console.log(...), // 插件注入
  //   _customProperties: Set(...)    // devtools 跟踪
  // }
  return store
}

/**
 * Extract the actions of a store type. Works with both a Setup Store or an
 * Options Store.
 */
export type StoreActions<SS> =
  SS extends Store<string, StateTree, _GettersTree<StateTree>, infer A>
    ? A
    : _ExtractActionsFromSetupStore<SS>

/**
 * Extract the getters of a store type. Works with both a Setup Store or an
 * Options Store.
 */
export type StoreGetters<SS> =
  SS extends Store<string, StateTree, infer G, _ActionsTree>
    ? _StoreWithGetters<G>
    : _ExtractGettersFromSetupStore<SS>

/**
 * Extract the state of a store type. Works with both a Setup Store or an
 * Options Store. Note this unwraps refs.
 */
export type StoreState<SS> =
  SS extends Store<string, infer S, _GettersTree<StateTree>, _ActionsTree>
    ? UnwrapRef<S>
    : _ExtractStateFromSetupStore<SS>

export interface SetupStoreHelpers {
  /**
   * Helper that wraps function so it can be tracked with $onAction when the
   * action is called **within the store**. This helper is rarely needed in
   * applications. It's intended for advanced use cases like Pinia Colada.
   *
   * @param fn - action to wrap
   * @param name - name of the action. Will be picked up by the store at creation
   */
  action: <Fn extends _Method>(fn: Fn, name?: string) => Fn
}

/**
 * Creates a `useStore` function that retrieves the store instance
 *
 * @param id - id of the store (must be unique)
 * @param options - options to define the store
 */
export function defineStore<
  Id extends string,
  S extends StateTree = {},
  G extends _GettersTree<S> = {},
  // cannot extends ActionsTree because we loose the typings
  A /* extends ActionsTree */ = {},
>(
  id: Id,
  options: Omit<DefineStoreOptions<Id, S, G, A>, 'id'>
): StoreDefinition<Id, S, G, A>

/**
 * Creates a `useStore` function that retrieves the store instance
 *
 * @param id - id of the store (must be unique)
 * @param storeSetup - function that defines the store
 * @param options - extra options
 */
export function defineStore<Id extends string, SS>(
  id: Id,
  storeSetup: (helpers: SetupStoreHelpers) => SS,
  options?: DefineSetupStoreOptions<
    Id,
    _ExtractStateFromSetupStore<SS>,
    _ExtractGettersFromSetupStore<SS>,
    _ExtractActionsFromSetupStore<SS>
  >
): StoreDefinition<
  Id,
  _ExtractStateFromSetupStore<SS>,
  _ExtractGettersFromSetupStore<SS>,
  _ExtractActionsFromSetupStore<SS>
>
// allows unused stores to be tree shaken
/*! #__NO_SIDE_EFFECTS__ */
//  Pinia 的用户入口 API，开发者用来定义并注册一个 store，比如：
// const useCounterStore = defineStore('counter', () => {
//   const count = ref(0)
//   const inc = () => count.value++
//   return { count, inc }
// })
export function defineStore(
  // TODO: add proper types from above
  id: any,
  setup?: any,
  setupOptions?: any
): StoreDefinition {
  let options:
    | DefineStoreOptions<
        string,
        StateTree,
        _GettersTree<StateTree>,
        _ActionsTree
      >
    | DefineSetupStoreOptions<
        string,
        StateTree,
        _GettersTree<StateTree>,
        _ActionsTree
      >

  // 第一段逻辑：识别是 setup store 还是 option store
  // 如果 setup 是函数，说明是 setup store，那真正的 options（比如 SSR 配置）是第三个参数 setupOptions
  // 否则就是 option store，那 setup 本身就是配置对象
  const isSetupStore = typeof setup === 'function'
  // the option store setup will contain the actual options in this case
  options = isSetupStore ? setupOptions : setup

  // useStore 函数 —— 获取 store 实例的工厂函数
  // 调用 defineStore(...) 的返回值是这个 useStore 函数，它会返回具体的 store 实例。
  function useStore(pinia?: Pinia | null, hot?: StoreGeneric): StoreGeneric {
    // 初始化 pinia 实例来源
    // 多种来源：
    // 明确传入的 pinia
    // 从当前组件注入上下文中找
    // 从 activePinia 中找（fallback）
    const hasContext = hasInjectionContext()
    pinia =
      // in test mode, ignore the argument provided as we can always retrieve a
      // pinia instance with getActivePinia()
      (__TEST__ && activePinia && activePinia._testing ? null : pinia) ||
      (hasContext ? inject(piniaSymbol, null) : null)

    // 确保在当前调用上下文中设置好活跃 Pinia 实例（类似 Vue 的 currentInstance）
    if (pinia) setActivePinia(pinia)

    // 开发警告
    if (__DEV__ && !activePinia) {
      // 你必须先 app.use(pinia) 才能使用 store，防止错误用法。
      throw new Error(
        `[🍍]: "getActivePinia()" was called but there was no active Pinia. Are you trying to use a store before calling "app.use(pinia)"?\n` +
          `See https://pinia.vuejs.org/core-concepts/outside-component-usage.html for help.\n` +
          `This will fail in production.`
      )
    }

    // 1. 强制 pinia 存在（已在前面设置了 activePinia）
    // 确保后续代码中 pinia 不为 null。
    pinia = activePinia!

    // 2. 如果尚未注册该 store，则创建
    if (!pinia._s.has(id)) {
      // pinia._s 是一个 Map<string, Store>，用于缓存所有创建过的 store。
      // creating the store registers it in `pinia._s`
      if (isSetupStore) {
        // 调用 setup() 或解析 state、actions
        // 返回一个 store 对象
        // 内部调用 pinia._s.set(id, store) 注册 store 到缓存中
        createSetupStore(id, setup, options, pinia)
      } else {
        createOptionsStore(id, options as any, pinia)
      }

      /* istanbul ignore else */
      if (__DEV__) {
        // @ts-expect-error: not the right inferred type
        useStore._pinia = pinia
      }
    }

    const store: StoreGeneric = pinia._s.get(id)!

    if (__DEV__ && hot) {
      // 构造一个临时 store，传入 hot = true
      // 调用 hot._hotUpdate() 更新旧 store 中的响应式引用
      // 删除这个临时热 store 的缓存
      const hotId = '__hot:' + id
      const newStore = isSetupStore
        ? createSetupStore(hotId, setup, options, pinia, true)
        : createOptionsStore(hotId, assign({}, options) as any, pinia, true)

      hot._hotUpdate(newStore)

      // cleanup the state properties and the store from the cache
      delete pinia.state.value[hotId]
      pinia._s.delete(hotId)
    }

    // 4. Devtools 调试支持
    // 将当前组件使用的 store 缓存到 component.proxy._pStores 上，供 devtools 使用
    if (__DEV__ && IS_CLIENT) {
      const currentInstance = getCurrentInstance()
      // save stores in instances to access them devtools
      if (
        currentInstance &&
        currentInstance.proxy &&
        // avoid adding stores that are just built for hot module replacement
        !hot
      ) {
        const vm = currentInstance.proxy
        const cache = '_pStores' in vm ? vm._pStores! : (vm._pStores = {})
        cache[id] = store
      }
    }

    // StoreGeneric cannot be casted towards Store
    return store as any
  }

  useStore.$id = id

  return useStore
}

/**
 * Return type of `defineStore()` with a setup function.
 * - `Id` is a string literal of the store's name
 * - `SS` is the return type of the setup function
 * @see {@link StoreDefinition}
 */
export interface SetupStoreDefinition<Id extends string, SS>
  extends StoreDefinition<
    Id,
    _ExtractStateFromSetupStore<SS>,
    _ExtractGettersFromSetupStore<SS>,
    _ExtractActionsFromSetupStore<SS>
  > {}
