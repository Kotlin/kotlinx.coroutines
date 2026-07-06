package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext

private object DarwinGlobalQueueDispatcher2 : CoroutineDispatcher() {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        val b: kotlinx.cinterop.UIntVarOf<UInt>
        val a: support.NativeSizeT
    }
}
