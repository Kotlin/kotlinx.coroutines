/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import kotlin.coroutines.*
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
                myThreadLocal.setForBlock(forBlockData) {
                    assertSame(myThreadLocal.get(), forBlockData)
                    launch {
                        assertSame(myThreadLocal.get(), forBlockData)
                    }
                    launch {
                        assertSame(myThreadLocal.get(), forBlockData)
                        // Modify value in child coroutine. Writes to the ThreadLocal and
                        // the (copied) ThreadLocalElement's memory are not visible to peer or
                        // ancestor coroutines, so this write is both threadsafe and coroutinesafe.
                        val innerCoroutineData = MyData()
                        myThreadLocal.setForBlock(innerCoroutineData) {
                            assertSame(myThreadLocal.get(), innerCoroutineData)
                        }
                        assertSame(myThreadLocal.get(), forBlockData) // Asserts value was restored.
                    }
                    launch {
                        val innerCoroutineData = MyData()
                        myThreadLocal.setForBlock(innerCoroutineData) {
                            assertSame(myThreadLocal.get(), innerCoroutineData)
                        }
                        assertSame(myThreadLocal.get(), forBlockData)
                    }
                }
                assertNull(myThreadLocal.get()) // Asserts value was restored to its origin
            }
        }
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

/**
 * A [ThreadContextElement] that implements copy semantics in [copyForChild].
 */
class CopyForChildCoroutineElement(val data: MyData?) : CopyableThreadContextElement<MyData?> {
    companion object Key : CoroutineContext.Key<CopyForChildCoroutineElement>

    override val key: CoroutineContext.Key<CopyForChildCoroutineElement>
        get() = Key

    override fun updateThreadContext(context: CoroutineContext): MyData? {
        val oldState = myThreadLocal.get()
        myThreadLocal.set(data)
        return oldState
    }

    override fun mergeForChild(overwritingElement: CoroutineContext.Element): CopyForChildCoroutineElement {
        TODO("Not used in tests")
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: MyData?) {
        myThreadLocal.set(oldState)
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
        return CopyForChildCoroutineElement(myThreadLocal.get())
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

