/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
    private val dispatcher: TestDispatcher
) : TestBase() {
    class TestDispatcher(val name: String, val block: () -> CoroutineDispatcher) {
        private var _value: CoroutineDispatcher? = null

        val value: CoroutineDispatcher
            get() = _value ?: block().also { _value = it }

        override fun toString(): String = name

        fun reset() {
            runCatching { (_value as? ExecutorCoroutineDispatcher)?.close() }
            _value = null
        }
    }

    private var caught: Throwable? = null
    private val latch = CountDownLatch(1)
    private var exceptionHandler = CoroutineExceptionHandler { _, t -> caught = t; latch.countDown() }
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
        dispatcher.reset()
        if (lazyOuterDispatcher.isInitialized()) lazyOuterDispatcher.value.close()
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "Element: {0}, dispatcher: {1}")
        fun dispatchers(): List<Array<Any>> {
            val elements = listOf<Any>(FailingRestore, FailingUpdate)
            val dispatchers = listOf<TestDispatcher>(
                TestDispatcher("Dispatchers.Unconfined") { Dispatchers.Unconfined },
                TestDispatcher("Dispatchers.Default") { Dispatchers.Default },
                TestDispatcher("Executors.newFixedThreadPool(1)") { Executors.newFixedThreadPool(1).asCoroutineDispatcher() },
                TestDispatcher("Executors.newScheduledThreadPool(1)") { Executors.newScheduledThreadPool(1).asCoroutineDispatcher() },
                TestDispatcher("ThrowingDispatcher") { ThrowingDispatcher },
                TestDispatcher("ThrowingDispatcher2") { ThrowingDispatcher2 }
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
        // Top-level throwing dispatcher may rethrow an exception right here
        runCatching {
            launch(NonCancellable + dispatcher.value + exceptionHandler + element) {}
        }
        checkException()
    }

    @Test
    fun testNestedElement() = runTest {
        // Top-level throwing dispatcher may rethrow an exception right here
        runCatching {
            launch(NonCancellable + dispatcher.value + exceptionHandler) {
                launch(element) { }
            }
        }
        checkException()
    }

    @Test
    fun testNestedDispatcherAndElement() = runTest {
        launch(lazyOuterDispatcher.value + NonCancellable + exceptionHandler) {
            launch(element + dispatcher.value) {  }
        }
        checkException()
    }

    private fun checkException() {
        latch.await(2, TimeUnit.SECONDS)
        val e = caught
        assertNotNull(e)
        // First condition -- failure in context element
        val firstCondition = e is CoroutinesInternalError && e.cause is TestException
        // Second condition -- failure from isDispatchNeeded (#880)
        val secondCondition = e is TestException
        assertTrue(firstCondition xor secondCondition)
    }
}
