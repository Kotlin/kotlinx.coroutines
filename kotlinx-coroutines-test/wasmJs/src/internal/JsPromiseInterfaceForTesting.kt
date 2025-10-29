package kotlinx.coroutines.test.internal

/* This is a declaration of JS's `Promise<JsAny>`. We need to keep it a separate class, because
`actual typealias TestResult = Promise<JsAny>` fails: you can't instantiate an `expect class` with a typealias to
a parametric class. So, we make a non-parametric class just for this. */
/**
 * @suppress
 */
@OptIn(ExperimentalWasmJsInterop::class)
@JsName("Promise")
public external class JsPromiseInterfaceForTesting : JsAny {
    /**
     * @suppress
     */
    public fun then(onFulfilled: ((JsAny) -> JsAny), onRejected: ((JsAny) -> JsAny)): JsPromiseInterfaceForTesting
    /**
     * @suppress
     */
    public fun then(onFulfilled: ((JsAny) -> JsAny)): JsPromiseInterfaceForTesting
}
