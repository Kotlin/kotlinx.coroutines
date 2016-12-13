package kotlinx.coroutines

import java.net.SocketAddress
import java.nio.ByteBuffer
import java.nio.channels.AsynchronousFileChannel
import java.nio.channels.AsynchronousServerSocketChannel
import java.nio.channels.AsynchronousSocketChannel
import java.nio.channels.CompletionHandler
import java.util.concurrent.CompletableFuture
import java.util.concurrent.TimeUnit
import javax.swing.SwingUtilities
import kotlin.coroutines.Continuation
import kotlin.coroutines.ResumeInterceptor
import kotlin.coroutines.startCoroutine

/**
 * Run asynchronous computations based on [c] coroutine parameter
 *
 * Execution starts immediately within the 'async' call and it runs until
 * the first suspension point is reached ('await' call with some CompletableFuture).
 * Remaining part of coroutine will be executed as it's passed into 'whenComplete'
 * call of awaited Future.
 *
 * @param c a coroutine representing asynchronous computations
 * @param continuationWrapper represents a function that wraps execution parts
 * between subsequent 'await' calls.
 * For example it could be 'SwingUtilities.invokeLater', providing ability to
 * call UI-related methods between 'await' calls
 *
 * @return CompletableFuture object representing result of computations
 */


fun <T> async(
        continuationWrapper: ContinuationWrapper? = null,
        c: suspend () -> T
): CompletableFuture<T> {
    val future = CompletableFuture<T>()

    c.startCoroutine(
            object : Continuation<T> {
                override fun resumeWithException(exception: Throwable) {
                    future.completeExceptionally(exception)
                }

                override fun resume(data: T) {
                    future.complete(data)
                }
            },

            if (continuationWrapper != null) {
                object: ResumeInterceptor {
                    override fun <P> interceptResume(data: P, continuation: Continuation<P>): Boolean {
                        continuationWrapper {
                            continuation.resume(data)
                        }

                        return true
                    }

                    override fun interceptResumeWithException(exception: Throwable, continuation: Continuation<*>): Boolean {
                        continuationWrapper {
                            continuation.resumeWithException(exception)
                        }

                        return true
                    }
                }
            }
            else {
                null
            }
    )

    return future
}

/**
 * Run asynchronous computations based on [c] coroutine parameter.
 * Continuation parts (everything besides awaited futures)
 *
 * @param c a coroutine representing asynchronous computations
 *
 * @return CompletableFuture object representing result of computations
 * @See async
 */
fun asyncUI(
        c: suspend () -> Unit
) {
    async({ SwingUtilities.invokeLater(it) }, c)
}

typealias ContinuationWrapper = (() -> Unit) -> Unit

suspend fun <V> await(f: CompletableFuture<V>): V =
        runWithCurrentContinuation {
            f.whenComplete { value, throwable ->
                if (throwable == null)
                    it.resume(value)
                else
                    it.resumeWithException(throwable)
            }
        }
//
// IO parts
//
suspend fun AsynchronousFileChannel.aRead(
        buf: ByteBuffer,
        position: Long
) = runWithCurrentContinuation<Int> { c ->
    this.read(buf, position, null, AsyncIOHandler(c))
}

suspend fun AsynchronousFileChannel.aWrite(
        buf: ByteBuffer,
        position: Long
) = runWithCurrentContinuation<Int> { c ->
    this.write(buf, position, null, AsyncIOHandler(c))
}

suspend fun AsynchronousServerSocketChannel.aAccept() =
        runWithCurrentContinuation<AsynchronousSocketChannel> { c ->
            this.accept(null, AsyncIOHandler(c))
        }

suspend fun AsynchronousSocketChannel.aConnect(
        socketAddress: SocketAddress
) = runWithCurrentContinuation<Unit> { c ->
    this.connect(socketAddress, null, AsyncVoidIOHandler(c))
}

suspend fun AsynchronousSocketChannel.aRead(
        buf: ByteBuffer,
        timeout: Long = 0L,
        timeUnit: TimeUnit = TimeUnit.MILLISECONDS
) = runWithCurrentContinuation<Int> { c ->
    this.read(buf, timeout, timeUnit, null, AsyncIOHandler(c))
}

suspend fun AsynchronousSocketChannel.aWrite(
        buf: ByteBuffer,
        timeout: Long = 0L,
        timeUnit: TimeUnit = TimeUnit.MILLISECONDS
) = runWithCurrentContinuation<Int> { c ->
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
