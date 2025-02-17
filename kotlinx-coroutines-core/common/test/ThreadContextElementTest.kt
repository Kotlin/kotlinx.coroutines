package kotlinx.coroutines

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

    @Test
    fun testWithContextJobAccess() = runTest {
        val captor = JobCaptor()
        val manuallyCaptured = ArrayList<Job>()
        withContext(captor) {
            manuallyCaptured += coroutineContext.job
            withContext(CoroutineName("undispatched")) {
                manuallyCaptured += coroutineContext.job
                withContext(Dispatchers.Default) {
                    manuallyCaptured += coroutineContext.job
                }
                // Context restored, captured again
                manuallyCaptured += coroutineContext.job
            }
            // Context restored, captured again
            manuallyCaptured += coroutineContext.job
        }
        assertEquals(manuallyCaptured, captor.capturees)
    }
}

private class JobCaptor() : ThreadContextElement<Unit> {

    val capturees: MutableList<Job> = mutableListOf()

    companion object Key : CoroutineContext.Key<MyElement>

    override val key: CoroutineContext.Key<*> get() = Key

    override fun updateThreadContext(context: CoroutineContext) {
        capturees.add(context.job)
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {
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
