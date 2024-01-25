package kotlinx.coroutines

import kotlin.coroutines.*

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()
    public actual val Main: MainCoroutineDispatcher
        get() = injectedMainDispatcher ?: mainDispatcher
    public actual val Unconfined: CoroutineDispatcher = kotlinx.coroutines.Unconfined

    private val mainDispatcher = JsMainDispatcher(Default, false)
    private var injectedMainDispatcher: MainCoroutineDispatcher? = null

    @PublishedApi
    internal fun injectMain(dispatcher: MainCoroutineDispatcher) {
        injectedMainDispatcher = dispatcher
    }
}

private class JsMainDispatcher(
    val delegate: CoroutineDispatcher,
    private val invokeImmediately: Boolean
) : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher =
        if (invokeImmediately) this else JsMainDispatcher(delegate, true)
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !invokeImmediately
    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)
    override fun toString(): String = toStringInternalImpl() ?: delegate.toString()
}
