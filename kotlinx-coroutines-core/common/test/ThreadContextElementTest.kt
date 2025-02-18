package kotlinx.coroutines

import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlinx.atomicfu.update
import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*
import kotlinx.coroutines.internal.*

class ThreadContextElementTest : TestBase() {
    interface TestThreadContextElement : ThreadContextElement<Int> {
        companion object Key : CoroutineContext.Key<TestThreadContextElement>
    }

    @Test
    fun testUpdatesAndRestores() = runTest {
        var updateCount = 0
        var restoreCount = 0
        val threadContextElement = object : TestThreadContextElement {
            override fun updateThreadContext(context: CoroutineContext): Int {
                updateCount++
                return 0
            }

            override fun restoreThreadContext(context: CoroutineContext, oldState: Int) {
                restoreCount++
            }

            override val key: CoroutineContext.Key<*>
                get() = TestThreadContextElement.Key
        }
        launch(Dispatchers.Unconfined + threadContextElement) {
            assertEquals(1, updateCount)
            assertEquals(0, restoreCount)
        }
        assertEquals(1, updateCount)
        assertEquals(1, restoreCount)
    }

    @Test
    fun testDispatched() = runTest {
        val mainDispatcher = coroutineContext[ContinuationInterceptor]!!
        val data = MyData()
        val element = MyElement(data)
        assertNull(threadContextElementThreadLocal.get())
        val job = launch(Dispatchers.Default + element) {
            assertSame(element, coroutineContext[MyElement])
            assertSame(data, threadContextElementThreadLocal.get())
            withContext(mainDispatcher) {
                assertSame(element, coroutineContext[MyElement])
                assertSame(data, threadContextElementThreadLocal.get())
            }
            assertSame(element, coroutineContext[MyElement])
            assertSame(data, threadContextElementThreadLocal.get())
        }
        assertNull(threadContextElementThreadLocal.get())
        job.join()
        assertNull(threadContextElementThreadLocal.get())
    }

    @Test
    fun testUndispatched() = runTest {
        val exceptionHandler = coroutineContext[CoroutineExceptionHandler]!!
        val data = MyData()
        val element = MyElement(data)
        val job = launch(
            context = Dispatchers.Default + exceptionHandler + element,
            start = CoroutineStart.UNDISPATCHED
        ) {
            assertSame(element, coroutineContext[MyElement])
            assertSame(data, threadContextElementThreadLocal.get())
            yield()
            assertSame(element, coroutineContext[MyElement])
            assertSame(data, threadContextElementThreadLocal.get())
        }
        assertNull(threadContextElementThreadLocal.get())
        job.join()
        assertNull(threadContextElementThreadLocal.get())
    }

    private class JobCaptor(val capturees: CopyOnWriteList<Event<Job>> = CopyOnWriteList()) : ThreadContextElement<Unit> {

        companion object Key : CoroutineContext.Key<MyElement>

        override val key: CoroutineContext.Key<*> get() = Key

        override fun updateThreadContext(context: CoroutineContext) {
            capturees.add(Event.Update(context.job))
        }

        override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {
            capturees.add(Event.Restore(context.job))
        }
    }

    /**
     * For stability of the test, it is important to make sure that
     * the parent job actually suspends when calling
     * `withContext(dispatcher2 + CoroutineName("dispatched"))`.
     *
     * Here this requirement is fulfilled by forcing execution on a single thread.
     * However, dispatching is performed with two non-equal dispatchers to force dispatching.
     *
     * Suspend of the parent coroutine [kotlinx.coroutines.DispatchedCoroutine.trySuspend] is out of the control of the test,
     * while being executed concurrently with resume of the child coroutine [kotlinx.coroutines.DispatchedCoroutine.tryResume].
     */
    @Test
    fun testWithContextJobAccess() = runTest {
        // Emulate non-equal dispatchers
        val dispatcher = Dispatchers.Default.limitedParallelism(1)
        val dispatcher1 = dispatcher.limitedParallelism(1, "dispatcher1")
        val dispatcher2 = dispatcher.limitedParallelism(1, "dispatcher2")
        val captor = JobCaptor()
        val manuallyCaptured = mutableListOf<Event<Job?>>()

        fun registerUpdate(job: Job?) = manuallyCaptured.add(Event.Update(job))
        fun registerRestore(job: Job?) = manuallyCaptured.add(Event.Restore(job))

        var rootJob: Job? = null
        withContext(captor + dispatcher1) {
            rootJob = coroutineContext.job
            registerUpdate(rootJob)
            var undispatchedJob: Job? = null
            withContext(CoroutineName("undispatched")) {
                undispatchedJob = coroutineContext.job
                registerUpdate(undispatchedJob)
                // These 2 restores and the corresponding next 2 updates happen only if the following `withContext`
                // call actually suspends.
                registerRestore(undispatchedJob)
                registerRestore(rootJob)
                // Without forcing of single backing thread the code inside `withContext`
                // may already complete at the moment when the parent coroutine decides
                // whether it needs to suspend or not.
                var dispatchedJob: Job? = null
                withContext(dispatcher2 + CoroutineName("dispatched")) {
                    dispatchedJob = coroutineContext.job
                    registerUpdate(dispatchedJob)
                }
                registerRestore(dispatchedJob)
                // Context restored, captured again
                registerUpdate(undispatchedJob)
            }
            registerRestore(undispatchedJob)
            // Context restored, captured again
            registerUpdate(rootJob)
        }
        registerRestore(rootJob)

        // Restores may be called concurrently to the update calls in other threads, so their order is not checked.
        val expected = manuallyCaptured.mapNotNull { (it as? Event.Update)?.value }.joinToString(separator = "\n")
        val actual = captor.capturees.mapNotNull { (it as? Event.Update)?.value }.joinToString(separator = "\n")
        assertEquals(expected, actual)
    }
}

internal class MyData

// declare thread local variable holding MyData
internal val threadContextElementThreadLocal = commonThreadLocal<MyData?>(Symbol("ThreadContextElementTest"))

// declare context element holding MyData
internal class MyElement(val data: MyData) : ThreadContextElement<MyData?> {
    // declare companion object for a key of this element in coroutine context
    companion object Key : CoroutineContext.Key<MyElement>

    // provide the key of the corresponding context element
    override val key: CoroutineContext.Key<MyElement>
        get() = Key

    // this is invoked before coroutine is resumed on current thread
    override fun updateThreadContext(context: CoroutineContext): MyData? {
        val oldState = threadContextElementThreadLocal.get()
        threadContextElementThreadLocal.set(data)
        return oldState
    }

    // this is invoked after coroutine has suspended on current thread
    override fun restoreThreadContext(context: CoroutineContext, oldState: MyData?) {
        threadContextElementThreadLocal.set(oldState)
    }
}

private sealed class Event<T> {
    class Update<T>(val value: T): Event<T>()
    class Restore<T>(val value: T): Event<T>()
}

private class CopyOnWriteList<T> private constructor(list: List<T>) {
    private val field = atomic(list)

    constructor() : this(emptyList())

    fun add(value: T) {
        field.loop { current ->
            val new = current + value
            if (field.compareAndSet(current, new)) return
        }
    }

    fun <R> mapNotNull(transform: (T) -> R): List<R> = field.value.mapNotNull(transform)
}
