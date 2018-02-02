package kotlinx.coroutines.experimental.io.jvm.javaio

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.*
import java.io.*
import java.util.concurrent.locks.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * Create blocking [java.io.InputStream] for this channel that does block every time the channel suspends at read
 * Similar to do reading in [runBlocking] however you can pass it to regular blocking API
 */
fun ByteReadChannel.toInputStream(parent: Job? = null): InputStream = InputAdapter(parent, this)

/**
 * Create blocking [java.io.OutputStream] for this channel that does block every time the channel suspends at write
 * Similar to do reading in [runBlocking] however you can pass it to regular blocking API
 */
fun ByteWriteChannel.toOutputStream(parent: Job? = null): OutputStream = OutputAdapter(parent, this)

private class InputAdapter(parent: Job?, private val channel: ByteReadChannel) : InputStream() {
    private val loop = object : BlockingAdapter(parent) {
        override suspend fun loop() {
            var rc = 0
            while (true) {
                val buffer = rendezvous(rc) as ByteArray
                rc = channel.readAvailable(buffer, offset, length)
                if (rc == -1) break
            }
        }
    }

    private var single: ByteArray? = null

    override fun available(): Int {
        return channel.availableForRead
    }

    @Synchronized
    override fun read(): Int {
        val buffer = single ?: ByteArray(1).also { single = it }
        loop.submitAndAwait(buffer, 0, 1)
        return buffer[0].toInt() and 0xff
    }

    @Synchronized
    override fun read(b: ByteArray?, off: Int, len: Int): Int {
        return loop.submitAndAwait(b!!, off, len)
    }

    @Synchronized
    override fun close() {
        super.close()
        channel.cancel()
        loop.shutdown()
    }
}

private val CloseToken = Any()
private val FlushToken = Any()

private class OutputAdapter(parent: Job?, private val channel: ByteWriteChannel) : OutputStream() {
    private val loop = object : BlockingAdapter(parent) {
        override suspend fun loop() {
            try {
                while (true) {
                    val task = rendezvous(0)
                    if (task === CloseToken) {
                        break
                    }
                    else if (task === FlushToken) {
                        channel.flush()
                        channel.closedCause?.let { throw it }
                    }
                    else if (task is ByteArray) channel.writeFully(task, offset, length)
                }
            } catch (t: Throwable) {
                if (t !is CancellationException) {
                    channel.close(t)
                }
                throw t
            } finally {
                if (!channel.close()) {
                    channel.closedCause?.let { throw it }
                }
            }
        }
    }

    private var single: ByteArray? = null

    @Synchronized
    override fun write(b: Int) {
        val buffer = single ?: ByteArray(1).also { single = it }
        buffer[0] = b.toByte()
        loop.submitAndAwait(buffer, 0, 1)
    }

    @Synchronized
    override fun write(b: ByteArray?, off: Int, len: Int) {
        loop.submitAndAwait(b!!, off, len)
    }

    @Synchronized
    override fun flush() {
        loop.submitAndAwait(FlushToken)
    }

    @Synchronized
    override fun close() {
        try {
            loop.submitAndAwait(CloseToken)
            loop.shutdown()
        } catch (t: Throwable) {
            throw IOException(t)
        }
    }
}

private abstract class BlockingAdapter(val parent: Job? = null) {
    private val end: Continuation<Unit> = object : Continuation<Unit> {
        override val context: CoroutineContext
            get() = if (parent != null) Unconfined + parent else EmptyCoroutineContext

        override fun resume(value: Unit) {
            var thread: Thread? = null
            result.value = -1
            state.update { current ->
                when (current) {
                    is Thread -> {
                        thread = current
                        Unit
                    }
                    this -> Unit
                    else -> return
                }
            }

            thread?.let { LockSupport.unpark(it) }
            disposable?.dispose()
        }

        override fun resumeWithException(exception: Throwable) {
            var thread: Thread? = null
            var continuation: Continuation<*>? = null

            result.value = -1
            state.update { current ->
                when (current) {
                    is Thread -> {
                        thread = current
                        exception
                    }
                    is Continuation<*> -> {
                        continuation = current
                        exception
                    }
                    this -> exception
                    else -> return
                }
            }

            thread?.let { LockSupport.unpark(it) }
            continuation?.resumeWithException(exception)

            if (exception !is CancellationException) {
                parent?.cancel(exception)
            }

            disposable?.dispose()
        }
    }

    @Suppress("LeakingThis")
    private val state: AtomicRef<Any> = atomic(this) // could be a thread, a continuation, Unit, an exception or this if not yet started
    private val result = atomic(0)
    private val disposable: DisposableHandle? = parent?.invokeOnCompletion { cause ->
        if (cause != null) {
            end.resumeWithException(cause)
        }
    }

    protected var offset: Int = 0
        private set
    protected var length: Int = 0
        private set

    init {
        val block: suspend () -> Unit = { loop() }
        block.startCoroutineUninterceptedOrReturn(end)
        require(state.value !== this)
    }

    protected abstract suspend fun loop()

    fun shutdown() {
        disposable?.dispose()
        end.resumeWithException(CancellationException("Stream closed"))
    }

    fun submitAndAwait(buffer: ByteArray, offset: Int, length: Int): Int {
        this.offset = offset
        this.length = length
        return submitAndAwait(buffer)
    }

    fun submitAndAwait(jobToken: Any): Int {
        val thread = Thread.currentThread()!!

        var cont: Continuation<Any>? = null

        state.update { value ->
            when (value) {
                is Continuation<*> -> {
                    @Suppress("UNCHECKED_CAST")
                    cont = value as Continuation<Any>
                    thread
                }
                is Unit -> {
                    return result.value
                }
                is Throwable -> {
                    throw value
                }
                is Thread -> throw IllegalStateException("There is already thread owning adapter")
                this -> throw IllegalStateException("Not yet started")
                else -> NoWhenBranchMatchedException()
            }
        }

        cont!!.resume(jobToken)

        while (state.value === thread) {
            LockSupport.park()
        }

        state.value.let { state ->
            if (state is Throwable) {
                throw state
            }
        }

        return result.value
    }

    @Suppress("NOTHING_TO_INLINE")
    protected suspend inline fun rendezvous(rc: Int): Any {
        result.value = rc

        return suspendCoroutineOrReturn { c ->
            var thread: Thread? = null

            state.update { value ->
                when (value) {
                    is Thread -> {
                        thread = value
                        c
                    }
                    this -> c
                    else -> throw IllegalStateException("Already suspended or in finished state")
                }
            }

            if (thread != null) {
                LockSupport.unpark(thread)
            }

            COROUTINE_SUSPENDED
        }
    }
}
