package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

/**
 * A coroutine job that is writing to a byte channel
 */
interface WriterJob : Job {
    /**
     * A reference to the channel that this coroutine is writing to
     */
    val channel: ByteReadChannel
}

interface WriterScope : CoroutineScope {
    val channel: ByteWriteChannel
}

fun writer(coroutineContext: CoroutineContext,
           channel: ByteChannel,
           block: suspend CoroutineScope.() -> Unit): WriterJob {
    val coroutine = WriterCoroutine(newCoroutineContext(coroutineContext), channel)
    coroutine.initParentJob(coroutineContext[Job])
    block.startCoroutine(coroutine, coroutine)
    return coroutine
}

fun writer(coroutineContext: CoroutineContext,
           autoFlush: Boolean = false,
           block: suspend CoroutineScope.() -> Unit): WriterJob = writer(coroutineContext, ByteChannel(autoFlush), block)

private class WriterCoroutine(ctx: CoroutineContext, channel: ByteChannel)
    : ByteChannelCoroutine(ctx, channel), WriterScope, WriterJob

