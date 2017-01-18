package kotlinx.coroutines.experimental.nio

import java.net.SocketAddress
import java.nio.ByteBuffer
import java.nio.channels.AsynchronousFileChannel
import java.nio.channels.AsynchronousServerSocketChannel
import java.nio.channels.AsynchronousSocketChannel
import java.nio.channels.CompletionHandler
import java.util.concurrent.TimeUnit
import kotlin.coroutines.Continuation
import kotlin.coroutines.suspendCoroutine

suspend fun AsynchronousFileChannel.aRead(
    buf: ByteBuffer,
    position: Long
) = suspendCoroutine<Int> { c ->
    this.read(buf, position, null, AsyncIOHandler(c))
}

suspend fun AsynchronousFileChannel.aWrite(
    buf: ByteBuffer,
    position: Long
) = suspendCoroutine<Int> { c ->
    this.write(buf, position, null, AsyncIOHandler(c))
}

suspend fun AsynchronousServerSocketChannel.aAccept() =
    suspendCoroutine<AsynchronousSocketChannel> { c ->
        this.accept(null, AsyncIOHandler(c))
    }

suspend fun AsynchronousSocketChannel.aConnect(
    socketAddress: SocketAddress
) = suspendCoroutine<Unit> { c ->
    this.connect(socketAddress, null, AsyncVoidIOHandler(c))
}

suspend fun AsynchronousSocketChannel.aRead(
    buf: ByteBuffer,
    timeout: Long = 0L,
    timeUnit: TimeUnit = TimeUnit.MILLISECONDS
) = suspendCoroutine<Int> { c ->
    this.read(buf, timeout, timeUnit, null, AsyncIOHandler(c))
}

suspend fun AsynchronousSocketChannel.aWrite(
    buf: ByteBuffer,
    timeout: Long = 0L,
    timeUnit: TimeUnit = TimeUnit.MILLISECONDS
) = suspendCoroutine<Int> { c ->
    this.write(buf, timeout, timeUnit, null, AsyncIOHandler(c))
}

private class AsyncIOHandler<E>(val c: Continuation<E>) : CompletionHandler<E, Nothing?> {
    override fun completed(result: E, attachment: Nothing?) {
        c.resume(result)
    }

    override fun failed(exc: Throwable, attachment: Nothing?) {
        c.resumeWithException(exc)
    }
}

private class AsyncVoidIOHandler(val c: Continuation<Unit>) : CompletionHandler<Void?, Nothing?> {
    override fun completed(result: Void?, attachment: Nothing?) {
        c.resume(Unit)
    }

    override fun failed(exc: Throwable, attachment: Nothing?) {
        c.resumeWithException(exc)
    }
}
