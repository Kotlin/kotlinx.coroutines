package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.LockFreeLinkedListHead
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import java.util.concurrent.locks.LockSupport
import kotlin.coroutines.Continuation
import kotlin.coroutines.startCoroutine

public interface EventLoop {
    public val thisEventLoop: CoroutineDispatcher
    public suspend fun yield()
}

@Throws(InterruptedException::class)
public fun <T> runEventLoop(block: suspend EventLoop.() -> T): T =
    EventLoopImpl<T>().also { block.startCoroutine(it, it.coroutine) }.coroutine.joinBlocking()

private class EventLoopImpl<T> : CoroutineDispatcher(), EventLoop {
    val thread: Thread = Thread.currentThread()
    val queue = LockFreeLinkedListHead()
    val coroutine = Coroutine()

    public override val thisEventLoop: CoroutineDispatcher = this

    public override suspend fun yield(): Unit = suspendCancellableCoroutine { cont ->
        val node = Resume(cont)
        schedule(node)
        cont.removeOnCompletion(node)
    }

    override fun isDispatchNeeded(): Boolean = Thread.currentThread() != thread

    override fun dispatch(block: Runnable) {
        schedule(Dispatch(block))
        queue.addLast(Dispatch(block))
    }

    fun schedule(node: LockFreeLinkedListNode) {
        check(queue.addLastIf(node) { coroutine.isActive }) {
            "EventLoop is already complete... cannot schedule any tasks"
        }
        LockSupport.unpark(thread)
    }

    inner class Coroutine : AbstractCoroutine<T>(this@EventLoopImpl) {
        override fun afterCompletion(state: Any?) {
            LockSupport.unpark(thread)
        }

        @Suppress("UNCHECKED_CAST")
        fun joinBlocking(): T {
            while (isActive) {
                if (Thread.interrupted()) throw InterruptedException().also { cancel(it) }
                (queue.removeFirstOrNull() as? Runnable)?.run() ?: LockSupport.park(this)
            }
            check(queue.isEmpty) { "There are still tasks in event loop queue... Stray coroutines?"}
            val state = getState()
            (state as? CompletedExceptionally)?.let { throw it.exception }
            return state as T
        }
    }

    class Dispatch(block: Runnable) : LockFreeLinkedListNode(), Runnable by block

    class Resume(val cont: Continuation<Unit>) : LockFreeLinkedListNode(), Runnable {
        override fun run() = cont.resume(Unit)
    }
}

