package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class ThreadContextElementNativeTest : TestBase() {

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
}

