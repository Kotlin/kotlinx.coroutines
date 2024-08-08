package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*
import kotlinx.coroutines.flow.*

class ThreadContextElementJvmTest : TestBase() {

    @Test
    fun testWithContext() = runTest {
        expect(1)
        newSingleThreadContext("withContext").use {
            val data = MyData()
            GlobalScope.async(Dispatchers.Default + MyElement(data)) {
                assertSame(data, threadContextElementThreadLocal.get())
                expect(2)

                val newData = MyData()
                GlobalScope.async(it + MyElement(newData)) {
                    assertSame(newData, threadContextElementThreadLocal.get())
                    expect(3)
                }.await()

                withContext(it + MyElement(newData)) {
                    assertSame(newData, threadContextElementThreadLocal.get())
                    expect(4)
                }

                GlobalScope.async(it) {
                    assertNull(threadContextElementThreadLocal.get())
                    expect(5)
                }.await()

                expect(6)
            }.await()
        }

        finish(7)
    }

    @Test
    fun testNonCopyableElementReferenceInheritedOnLaunch() = runTest {
        var parentElement: MyElement? = null
        var inheritedElement: MyElement? = null

        newSingleThreadContext("withContext").use {
            withContext(it + MyElement(MyData())) {
                parentElement = coroutineContext[MyElement.Key]
                launch {
                    inheritedElement = coroutineContext[MyElement.Key]
                }
            }
        }

        assertSame(inheritedElement, parentElement,
            "Inner and outer coroutines did not have the same object reference to a" +
                " ThreadContextElement that did not override `copyForChildCoroutine()`")
    }

    @Test
    fun testCopyableElementCopiedOnLaunch() = runTest {
        var parentElement: CopyForChildCoroutineElement? = null
        var inheritedElement: CopyForChildCoroutineElement? = null

        newSingleThreadContext("withContext").use {
            withContext(it + CopyForChildCoroutineElement(MyData())) {
                parentElement = coroutineContext[CopyForChildCoroutineElement.Key]
                launch {
                    inheritedElement = coroutineContext[CopyForChildCoroutineElement.Key]
                }
            }
        }

        assertNotSame(inheritedElement, parentElement,
            "Inner coroutine did not copy its copyable ThreadContextElement.")
    }

    @Test
    fun testCopyableThreadContextElementImplementsWriteVisibility() = runTest {
        newFixedThreadPoolContext(nThreads = 4, name = "withContext").use {
            withContext(it + CopyForChildCoroutineElement(MyData())) {
                val forBlockData = MyData()
                threadContextElementThreadLocal.setForBlock(forBlockData) {
                    assertSame(threadContextElementThreadLocal.get(), forBlockData)
                    launch {
                        assertSame(threadContextElementThreadLocal.get(), forBlockData)
                    }
                    launch {
                        assertSame(threadContextElementThreadLocal.get(), forBlockData)
                        // Modify value in child coroutine. Writes to the ThreadLocal and
                        // the (copied) ThreadLocalElement's memory are not visible to peer or
                        // ancestor coroutines, so this write is both threadsafe and coroutinesafe.
                        val innerCoroutineData = MyData()
                        threadContextElementThreadLocal.setForBlock(innerCoroutineData) {
                            assertSame(threadContextElementThreadLocal.get(), innerCoroutineData)
                        }
                        assertSame(threadContextElementThreadLocal.get(), forBlockData) // Asserts value was restored.
                    }
                    launch {
                        val innerCoroutineData = MyData()
                        threadContextElementThreadLocal.setForBlock(innerCoroutineData) {
                            assertSame(threadContextElementThreadLocal.get(), innerCoroutineData)
                        }
                        assertSame(threadContextElementThreadLocal.get(), forBlockData)
                    }
                }
                assertNull(threadContextElementThreadLocal.get()) // Asserts value was restored to its origin
            }
        }
    }

    class JobCaptor(val capturees: ArrayList<Job> = ArrayList()) : ThreadContextElement<Unit> {

        companion object Key : CoroutineContext.Key<MyElement>

        override val key: CoroutineContext.Key<*> get() = Key

        override fun updateThreadContext(context: CoroutineContext) {
            capturees.add(context.job)
        }

        override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {
        }
    }

    @Test
    fun testWithContextJobAccess() = runTest {
        val captor = JobCaptor()
        val manuallyCaptured = ArrayList<Job>()
        runBlocking(captor) {
            manuallyCaptured += coroutineContext.job
            withContext(CoroutineName("undispatched")) {
                manuallyCaptured += coroutineContext.job
                withContext(Dispatchers.IO) {
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

    @Test
    fun testThreadLocalFlowOn() = runTest {
        val myData = MyData()
        threadContextElementThreadLocal.set(myData)
        expect(1)
        flow {
            assertEquals(myData, threadContextElementThreadLocal.get())
            emit(1)
        }
            .flowOn(threadContextElementThreadLocal.asContextElement() + Dispatchers.Default)
            .single()
        threadContextElementThreadLocal.set(null)
        finish(2)
    }
}

/**
 * A [ThreadContextElement] that implements copy semantics in [copyForChild].
 */
internal class CopyForChildCoroutineElement(val data: MyData?) : CopyableThreadContextElement<MyData?> {
    companion object Key : CoroutineContext.Key<CopyForChildCoroutineElement>

    override val key: CoroutineContext.Key<CopyForChildCoroutineElement>
        get() = Key

    override fun updateThreadContext(context: CoroutineContext): MyData? {
        val oldState = threadContextElementThreadLocal.get()
        threadContextElementThreadLocal.set(data)
        return oldState
    }

    override fun mergeForChild(overwritingElement: CoroutineContext.Element): CopyForChildCoroutineElement {
        TODO("Not used in tests")
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: MyData?) {
        threadContextElementThreadLocal.set(oldState)
    }

    /**
     * At coroutine launch time, the _current value of the ThreadLocal_ is inherited by the new
     * child coroutine, and that value is copied to a new, unique, ThreadContextElement memory
     * reference for the child coroutine to use uniquely.
     *
     * n.b. the value copied to the child must be the __current value of the ThreadLocal__ and not
     * the value initially passed to the ThreadContextElement in order to reflect writes made to the
     * ThreadLocal between coroutine resumption and the child coroutine launch point. Those writes
     * will be reflected in the parent coroutine's [CopyForChildCoroutineElement] when it yields the
     * thread and calls [restoreThreadContext].
     */
    override fun copyForChild(): CopyForChildCoroutineElement {
        return CopyForChildCoroutineElement(threadContextElementThreadLocal.get())
    }
}


/**
 * Calls [block], setting the value of [this] [ThreadLocal] for the duration of [block].
 *
 * When a [CopyForChildCoroutineElement] for `this` [ThreadLocal] is used within a
 * [CoroutineContext], a ThreadLocal set this way will have the "correct" value expected lexically
 * at every statement reached, whether that statement is reached immediately, across suspend and
 * redispatch within one coroutine, or within a child coroutine. Writes made to the `ThreadLocal`
 * by child coroutines will not be visible to the parent coroutine. Writes made to the `ThreadLocal`
 * by the parent coroutine _after_ launching a child coroutine will not be visible to that child
 * coroutine.
 */
private inline fun <ThreadLocalT, OutputT> ThreadLocal<ThreadLocalT>.setForBlock(
    value: ThreadLocalT,
    crossinline block: () -> OutputT
) {
    val priorValue = get()
    set(value)
    block()
    set(priorValue)
}

