package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.newCoroutineContext
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * A coroutine job that is reading from a byte channel
 */
interface ReaderJob : Job {
    /**
     * A reference to the channel that this coroutine is reading from
     */
    val channel: ByteWriteChannel
}

interface ReaderScope : CoroutineScope {
    val channel: ByteReadChannel
}

fun reader(coroutineContext: CoroutineContext,
           channel: ByteChannel,
           block: suspend ReaderScope.() -> Unit): ReaderJob {
    val coroutine = ReaderCoroutine(newCoroutineContext(coroutineContext), channel)
    coroutine.initParentJob(coroutineContext[Job])
    block.startCoroutine(coroutine, coroutine)
    return coroutine
}

fun reader(coroutineContext: CoroutineContext,
           autoFlush: Boolean = false,
           block: suspend ReaderScope.() -> Unit): ReaderJob = reader(coroutineContext, ByteChannel(autoFlush), block)

private class ReaderCoroutine(context: CoroutineContext, channel: ByteChannel)
    : ByteChannelCoroutine(context, channel), ReaderJob, ReaderScope
