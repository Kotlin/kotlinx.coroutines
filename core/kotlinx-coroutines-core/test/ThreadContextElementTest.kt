/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.Test
import kotlin.coroutines.experimental.*
import kotlin.test.*

class ThreadContextElementTest : TestBase() {

    @Test
    fun testExample() = runTest {
        val exceptionHandler = coroutineContext[CoroutineExceptionHandler]!!
        val mainDispatcher = coroutineContext[ContinuationInterceptor]!!
        val mainThread = Thread.currentThread()
        val data = MyData()
        val element = MyElement(data)
        assertNull(myThreadLocal.get())
        val job = GlobalScope.launch(element + exceptionHandler) {
            assertTrue(mainThread != Thread.currentThread())
            assertSame(element, coroutineContext[MyElement])
            assertSame(data, myThreadLocal.get())
            withContext(mainDispatcher) {
                assertSame(mainThread, Thread.currentThread())
                assertSame(element, coroutineContext[MyElement])
                assertSame(data, myThreadLocal.get())
            }
            assertTrue(mainThread != Thread.currentThread())
            assertSame(element, coroutineContext[MyElement])
            assertSame(data, myThreadLocal.get())
        }
        assertNull(myThreadLocal.get())
        job.join()
        assertNull(myThreadLocal.get())
    }

    @Test
    fun testUndispatched()= runTest {
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


    @Test
    fun testWithContext() = runTest {
        expect(1)
        newSingleThreadContext("withContext").use {
            val data = MyData()
            GlobalScope.async(Dispatchers.Default + MyElement(data)) {
                assertSame(data, myThreadLocal.get())
                expect(2)

                val newData = MyData()
                GlobalScope.async(it + MyElement(newData)) {
                    assertSame(newData, myThreadLocal.get())
                    expect(3)
                }.await()

                withContext(it + MyElement(newData)) {
                    assertSame(newData, myThreadLocal.get())
                    expect(4)
                }

                GlobalScope.async(it) {
                    assertNull(myThreadLocal.get())
                    expect(5)
                }.await()

                expect(6)
            }.await()
        }

        finish(7)
    }
}

class MyData

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
