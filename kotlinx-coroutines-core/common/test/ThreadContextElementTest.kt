package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*

class ThreadContextElementTest: TestBase() {

    @Test
    fun testUndispatched() = runTest {
        val exceptionHandler = coroutineContext[CoroutineExceptionHandler]!!
        val data = MyData()
        val element = MyElement(data)
        val job = GlobalScope.launch(
            context = Dispatchers.Default + exceptionHandler + element,
            start = CoroutineStart.UNDISPATCHED
        ) {
            assertSame(data, myThreadLocal.get())
            yield()
            assertSame(data, myThreadLocal.get())
        }
        assertNull(myThreadLocal.get())
        job.join()
        assertNull(myThreadLocal.get())
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
        val executor = Executors.newSingleThreadExecutor()
        // Emulate non-equal dispatchers
        val executor1 = object : ExecutorService by executor {}
        val executor2 = object : ExecutorService by executor {}
        val dispatcher1 = executor1.asCoroutineDispatcher()
        val dispatcher2 = executor2.asCoroutineDispatcher()
        val captor = JobCaptor()
        val manuallyCaptured = mutableListOf<String>()

        fun registerUpdate(job: Job?) = manuallyCaptured.add("Update: $job")
        fun registerRestore(job: Job?) = manuallyCaptured.add("Restore: $job")

        var rootJob: Job? = null
        runBlocking(captor + dispatcher1) {
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
        val expected = manuallyCaptured.filter { it.startsWith("Update: ") }.joinToString(separator = "\n")
        val actual = captor.capturees.filter { it.startsWith("Update: ") }.joinToString(separator = "\n")
        assertEquals(expected, actual)
        executor.shutdownNow()
    }

    @Test
    fun testThreadLocalFlowOn() = runTest {
        val myData = MyData()
        myThreadLocal.set(myData)
        expect(1)
        flow {
            assertEquals(myData, myThreadLocal.get())
            emit(1)
        }
            .flowOn(myThreadLocal.asContextElement() + Dispatchers.Default)
            .single()
        myThreadLocal.set(null)
        finish(2)
    }
}

class MyData

class JobCaptor(val capturees: MutableList<String> = CopyOnWriteArrayList()) : ThreadContextElement<Unit> {

    companion object Key : CoroutineContext.Key<MyElement>

    override val key: CoroutineContext.Key<*> get() = Key

    override fun updateThreadContext(context: CoroutineContext) {
        capturees.add("Update: ${context.job}")
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {
        capturees.add("Restore: ${context.job}")
    }
}

// declare thread local variable holding MyData
private val myThreadLocal = ThreadLocal<MyData?>()

// declare context element holding MyData
class MyElement(val data: MyData) : ThreadContextElement<MyData?> {
    // declare companion object for a key of this element in coroutine context
    companion object Key : CoroutineContext.Key<MyElement>

    // provide the key of the corresponding context element
    override val key: CoroutineContext.Key<MyElement>
        get() = Key

    // this is invoked before coroutine is resumed on current thread
    override fun updateThreadContext(context: CoroutineContext): MyData? {
        val oldState = myThreadLocal.get()
        myThreadLocal.set(data)
        return oldState
    }

    // this is invoked after coroutine has suspended on current thread
    override fun restoreThreadContext(context: CoroutineContext, oldState: MyData?) {
        myThreadLocal.set(oldState)
    }
}
