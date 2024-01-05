/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.seconds

/**
 * The number of milliseconds that is sure not to pass [assertRunsFast].
 */
const val SLOW = 100_000L

/**
 * Asserts that a block completed within [timeout].
 */
inline fun <T> assertRunsFast(timeout: Duration, block: () -> T): T {
    val result: T
    val elapsed = TimeSource.Monotonic.measureTime { result = block() }
    assertTrue("Should complete in $timeout, but took $elapsed") { elapsed < timeout }
    return result
}

/**
 * Asserts that a block completed within two seconds.
 */
inline fun <T> assertRunsFast(block: () -> T): T = assertRunsFast(2.seconds, block)

/**
 * A class inheriting from which allows to check the execution order inside tests.
 *
 * @see TestBase
 */
open class OrderedExecutionTestBase {
    private val actionIndex = atomic(0)
    private val finished = atomic(false)

    /** Expect the next action to be [index] in order. */
    protected fun expect(index: Int) {
        val wasIndex = actionIndex.incrementAndGet()
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex" }
    }

    /** Expect this action to be final, with the given [index]. */
    protected fun finish(index: Int) {
        expect(index)
        check(!finished.getAndSet(true)) { "Should call 'finish(...)' at most once" }
    }

    @AfterTest
    fun ensureFinishCalls() {
        assertTrue(finished.value || actionIndex.value == 0, "Expected `finish` to be called")
    }
}

fun <T> T.void() { }

@OptionalExpectation
expect annotation class NoJs()

@OptionalExpectation
expect annotation class NoNative()

expect val isStressTest: Boolean
expect val stressTestMultiplier: Int
expect val stressTestMultiplierSqrt: Int

/**
 * The result of a multiplatform asynchronous test.
 * Aliases into Unit on K/JVM and K/N, and into Promise on K/JS.
 */
@Suppress("NO_ACTUAL_FOR_EXPECT")
public expect class TestResult

public expect val isNative: Boolean

public expect open class TestBase constructor() {
    /*
     * In common tests we emulate parameterized tests
     * by iterating over parameters space in the single @Test method.
     * This kind of tests is too slow for JS and does not fit into
     * the default Mocha timeout, so we're using this flag to bail-out
     * and run such tests only on JVM and K/N.
     */
    public val isBoundByJsTestTimeout: Boolean
    public fun error(message: Any, cause: Throwable? = null): Nothing
    public fun expect(index: Int)
    public fun expectUnreached()
    public fun finish(index: Int)
    public fun ensureFinished() // Ensures that 'finish' was invoked
    public fun reset() // Resets counter and finish flag. Workaround for parametrized tests absence in common
    public fun println(message: Any?)

    public fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    ): TestResult
}

public suspend inline fun hang(onCancellation: () -> Unit) {
    try {
        suspendCancellableCoroutine<Unit> { }
    } finally {
        onCancellation()
    }
}

public inline fun <reified T : Throwable> assertFailsWith(block: () -> Unit) {
    try {
        block()
        error("Should not be reached")
    } catch (e: Throwable) {
        assertTrue(e is T)
    }
}

public suspend inline fun <reified T : Throwable> assertFailsWith(flow: Flow<*>) {
    try {
        flow.collect()
        fail("Should be unreached")
    } catch (e: Throwable) {
        assertTrue(e is T, "Expected exception ${T::class}, but had $e instead")
    }
}

public suspend fun Flow<Int>.sum() = fold(0) { acc, value -> acc + value }
public suspend fun Flow<Long>.longSum() = fold(0L) { acc, value -> acc + value }


// data is added to avoid stacktrace recovery because CopyableThrowable is not accessible from common modules
public class TestException(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestException1(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestException2(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestException3(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestCancellationException(message: String? = null, private val data: Any? = null) : CancellationException(message)
public class TestRuntimeException(message: String? = null, private val data: Any? = null) : RuntimeException(message)
public class RecoverableTestException(message: String? = null) : RuntimeException(message)
public class RecoverableTestCancellationException(message: String? = null) : CancellationException(message)

public fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
    val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
    return object : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean =
            dispatcher.isDispatchNeeded(context)
        override fun dispatch(context: CoroutineContext, block: Runnable) =
            dispatcher.dispatch(context, block)
    }
}

public suspend fun wrapperDispatcher(): CoroutineContext = wrapperDispatcher(coroutineContext)

class BadClass {
    override fun equals(other: Any?): Boolean = error("equals")
    override fun hashCode(): Int = error("hashCode")
    override fun toString(): String = error("toString")
}

public expect val isJavaAndWindows: Boolean
