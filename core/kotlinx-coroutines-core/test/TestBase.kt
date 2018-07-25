/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.*
import kotlinx.coroutines.experimental.scheduling.*
import java.util.concurrent.atomic.*

/**
 * Base class for tests, so that tests for predictable scheduling of actions in multiple coroutines sharing a single
 * thread can be written. Use it like this:
 *
 * ```
 * class MyTest {
 *    @Test
 *    fun testSomething() = runBlocking<Unit> { // run in the context of the main thread
 *        expect(1) // initiate action counter
 *        val job = launch(context) { // use the context of the main thread
 *           expect(3) // the body of this coroutine in going to be executed in the 3rd step
 *        }
 *        expect(2) // launch just scheduled coroutine for exectuion later, so this line is executed second
 *        yield() // yield main thread to the launched job
 *        finish(4) // fourth step is the last one. `finish` must be invoked or test fails
 *    }
 * }
 * ```
 */
public actual open class TestBase actual constructor() {
    /**
     * Is `true` when nightly stress test is done.
     */
    public actual val isStressTest = System.getProperty("stressTest") != null

    public val stressTestMultiplierSqrt = if (isStressTest) 5 else 1

    /**
     * Multiply various constants in stress tests by this factor, so that they run longer during nightly stress test.
     */
    public actual val stressTestMultiplier = stressTestMultiplierSqrt * stressTestMultiplierSqrt

    private var actionIndex = AtomicInteger()
    private var finished = AtomicBoolean()
    private var error = AtomicReference<Throwable>()

    /**
     * Throws [IllegalStateException] like `error` in stdlib, but also ensures that the test will not
     * complete successfully even if this exception is consumed somewhere in the test.
     */
    @Suppress("ACTUAL_FUNCTION_WITH_DEFAULT_ARGUMENTS")
    public actual fun error(message: Any, cause: Throwable? = null): Nothing {
        val exception = IllegalStateException(message.toString(), cause)
        error.compareAndSet(null, exception)
        throw exception
    }

    private fun printError(message: String, cause: Throwable) {
        error.compareAndSet(null, cause)
        println("$message: $cause")
        cause.printStackTrace(System.out)
    } 

    /**
     * Throws [IllegalStateException] when `value` is false like `check` in stdlib, but also ensures that the
     * test will not complete successfully even if this exception is consumed somewhere in the test.
     */
    public inline fun check(value: Boolean, lazyMessage: () -> Any): Unit {
        if (!value) error(lazyMessage())
    }

    /**
     * Asserts that this invocation is `index`-th in the execution sequence (counting from one).
     */
    public actual fun expect(index: Int) {
        val wasIndex = actionIndex.incrementAndGet()
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex" }
    }

    /**
     * Asserts that this line is never executed.
     */
    public actual fun expectUnreached() {
        error("Should not be reached")
    }

    /**
     * Asserts that this it the last action in the test. It must be invoked by any test that used [expect].
     */
    public actual fun finish(index: Int) {
        expect(index)
        check(!finished.getAndSet(true)) { "Should call 'finish(...)' at most once" }
    }

    public actual fun reset() {
        check(actionIndex.get() == 0 || finished.get()) { "Expecting that 'finish(...)' was invoked, but it was not" }
        actionIndex.set(0)
        finished.set(false)
    }

    private lateinit var threadsBefore: Set<Thread>
    private val SHUTDOWN_TIMEOUT = 10_000L // 10s at most to wait

    @Before
    fun before() {
        initPoolsBeforeTest()
        threadsBefore = currentThreads()
    }

    @After
    fun onCompletion() {
        error.get()?.let { throw it }
        check(actionIndex.get() == 0 || finished.get()) { "Expecting that 'finish(...)' was invoked, but it was not" }
        shutdownPoolsAfterTest()
        checkTestThreads(threadsBefore)
    }

    fun initPoolsBeforeTest() {
        CommonPool.usePrivatePool()
        if (useCoroutinesScheduler) (DefaultDispatcher as ExperimentalCoroutineDispatcher).usePrivateScheduler()
    }

    fun shutdownPoolsAfterTest() {
        CommonPool.shutdown(SHUTDOWN_TIMEOUT)
        if (useCoroutinesScheduler) (DefaultDispatcher as ExperimentalCoroutineDispatcher).shutdown(SHUTDOWN_TIMEOUT)
        DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT)
    }

    @Suppress("ACTUAL_WITHOUT_EXPECT", "ACTUAL_FUNCTION_WITH_DEFAULT_ARGUMENTS")
    public actual fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    ) {
        var exCount = 0
        var ex: Throwable? = null
        try {
            runBlocking(block = block, context = CoroutineExceptionHandler { context, e ->
                if (e is CancellationException) return@CoroutineExceptionHandler // are ignored
                exCount++
                when {
                    exCount > unhandled.size ->
                        printError("Too many unhandled exceptions $exCount, expected ${unhandled.size}, got: $e", e)
                    !unhandled[exCount - 1](e) ->
                        printError("Unhandled exception was unexpected: $e", e)
                }
                context[Job]?.cancel(e)
            })
        } catch (e: Throwable) {
            ex = e
            if (expected != null) {
                if (!expected(e))
                    error("Unexpected exception: $e", e)
            } else
                throw e
        } finally {
            if (ex == null && expected != null) error("Exception was expected but none produced")
        }
        if (exCount < unhandled.size)
            error("Too few unhandled exceptions $exCount, expected ${unhandled.size}")
    }
}
