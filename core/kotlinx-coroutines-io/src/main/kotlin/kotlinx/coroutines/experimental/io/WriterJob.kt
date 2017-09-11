package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.newCoroutineContext
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

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
           block: suspend WriterScope.() -> Unit): WriterJob {
    val coroutine = WriterCoroutine(newCoroutineContext(coroutineContext), channel)
    coroutine.initParentJob(coroutineContext[Job])
    block.startCoroutine(coroutine, coroutine)
    return coroutine
}

fun writer(coroutineContext: CoroutineContext,
           autoFlush: Boolean = false,
           block: suspend WriterScope.() -> Unit): WriterJob = writer(coroutineContext, ByteChannel(autoFlush), block)

private class WriterCoroutine(ctx: CoroutineContext, channel: ByteChannel)
    : ByteChannelCoroutine(ctx, channel), WriterScope, WriterJob

