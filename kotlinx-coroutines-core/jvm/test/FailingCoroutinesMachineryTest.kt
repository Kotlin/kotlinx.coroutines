/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

@RunWith(Parameterized::class)
class FailingCoroutinesMachineryTest(
    private val element: CoroutineContext.Element,
    private val dispatcher: CoroutineDispatcher
) : TestBase() {

    private var caught: Throwable? = null
    private val latch = CountDownLatch(1)
    private var exceptionHandler = CoroutineExceptionHandler { _, t -> caught = t;latch.countDown() }
    private val lazyOuterDispatcher = lazy { newFixedThreadPoolContext(1, "") }

    private object FailingUpdate : ThreadContextElement<Unit> {
        private object Key : CoroutineContext.Key<MyElement>

        override val key: CoroutineContext.Key<*> get() = Key

        override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {
        }

        override fun updateThreadContext(context: CoroutineContext) {
            throw TestException("Prevent a coroutine from starting right here for some reason")
        }

        override fun toString() = "FailingUpdate"
    }

    private object FailingRestore : ThreadContextElement<Unit> {
        private object Key : CoroutineContext.Key<MyElement>

        override val key: CoroutineContext.Key<*> get() = Key

        override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {
            throw TestException("Prevent a coroutine from starting right here for some reason")
        }

        override fun updateThreadContext(context: CoroutineContext) {
        }

        override fun toString() = "FailingRestore"
    }

    private object ThrowingDispatcher : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            throw TestException()
        }

        override fun toString() = "ThrowingDispatcher"
    }

    private object ThrowingDispatcher2 : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            block.run()
        }

        override fun isDispatchNeeded(context: CoroutineContext): Boolean {
            throw TestException()
        }

        override fun toString() = "ThrowingDispatcher2"
    }

    @After
    fun tearDown() {
        runCatching { (dispatcher as? ExecutorCoroutineDispatcher)?.close() }
        if (lazyOuterDispatcher.isInitialized()) lazyOuterDispatcher.value.close()
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "Element: {0}, dispatcher: {1}")
        fun dispatchers(): List<Array<Any>> {
            val elements = listOf<Any>(FailingRestore, FailingUpdate)
            val dispatchers = listOf<Any>(
                Dispatchers.Unconfined,
                Dispatchers.Default,
                Executors.newFixedThreadPool(1).asCoroutineDispatcher(),
                Executors.newScheduledThreadPool(1).asCoroutineDispatcher(),
                ThrowingDispatcher, ThrowingDispatcher2
            )

            return elements.flatMap { element ->
                dispatchers.map { dispatcher ->
                    arrayOf(element, dispatcher)
                }
            }
        }
    }

    @Test
    fun testElement() = runTest {
        launch(NonCancellable + dispatcher + exceptionHandler + element) {}
        checkException()
    }

    @Test
    fun testNestedElement() = runTest {
        launch(NonCancellable + dispatcher + exceptionHandler) {
            launch(element) {  }
        }
        checkException()
    }

    @Test
    fun testNestedDispatcherAndElement() = runTest {
        launch(lazyOuterDispatcher.value + NonCancellable + exceptionHandler) {
            launch(element + dispatcher) {  }
        }
        checkException()
    }

    private fun checkException() {
        latch.await(2, TimeUnit.SECONDS)
        val e = caught
        assertNotNull(e)
        // First condition -- failure in context element
        val firstCondition = e is DispatchException && e.cause is TestException
        // Second condition -- failure from isDispatchNeeded (#880)
        val secondCondition = e is TestException
        assertTrue(firstCondition xor secondCondition)
    }
}
