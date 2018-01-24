package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

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
           parent: Job? = null,
           block: suspend ReaderScope.() -> Unit): ReaderJob {
    val newContext = newCoroutineContext(coroutineContext, parent)
    val coroutine = ReaderCoroutine(newContext, channel)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine
}

fun reader(coroutineContext: CoroutineContext,
           autoFlush: Boolean = false,
           parent: Job? = null,
           block: suspend ReaderScope.() -> Unit): ReaderJob {
    val channel = ByteChannel(autoFlush) as ByteBufferChannel
    val job = reader(coroutineContext, channel, parent, block)
    channel.attachJob(job)
    return job
}

private class ReaderCoroutine(context: CoroutineContext, channel: ByteChannel)
    : ByteChannelCoroutine(context, channel), ReaderJob, ReaderScope
