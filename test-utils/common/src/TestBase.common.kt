@file:Suppress("unused")
package kotlinx.coroutines.testing

import kotlinx.atomicfu.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
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
 * Whether the tests should trace their calls to `expect` and `finish` with `println`.
 * `false` by default. On the JVM, can be set to `true` by setting the `test.verbose` system property.
 */
expect val VERBOSE: Boolean

interface OrderedExecution {
    /** Expect the next action to be [index] in order. */
    fun expect(index: Int)

    /** Expect this action to be final, with the given [index]. */
    fun finish(index: Int)

    /** * Asserts that this line is never executed. */
    fun expectUnreached()

    /**
     * Checks that [finish] was called.
     *
     * By default, it is allowed to not call [finish] if [expect] was not called.
     * This is useful for tests that don't check the ordering of events.
     * When [allowNotUsingExpect] is set to `false`, it is an error to not call [finish] in any case.
     */
    fun checkFinishCall(allowNotUsingExpect: Boolean = true)

    class Impl : OrderedExecution {
        private val actionIndex = atomic(0)

        override fun expect(index: Int) {
            val wasIndex = actionIndex.incrementAndGet()
            if (VERBOSE) println("expect($index), wasIndex=$wasIndex")
            check(index == wasIndex) {
                if (wasIndex < 0) "Expecting action index $index but it is actually finished"
                else "Expecting action index $index but it is actually $wasIndex"
            }
        }

        override fun finish(index: Int) {
            val wasIndex = actionIndex.getAndSet(Int.MIN_VALUE) + 1
            if (VERBOSE) println("finish($index), wasIndex=${if (wasIndex < 0) "finished" else wasIndex}")
            check(index == wasIndex) {
                if (wasIndex < 0) "Finished more than once"
                else "Finishing with action index $index but it is actually $wasIndex"
            }
        }

        override fun expectUnreached() {
            error("Should not be reached, ${
                actionIndex.value.let {
                    when {
                        it < 0 -> "already finished"
                        it == 0 -> "'expect' was not called yet"
                        else -> "the last executed action was $it"
                    }
                }
            }")
        }

        override fun checkFinishCall(allowNotUsingExpect: Boolean) {
            actionIndex.value.let {
                assertTrue(
                    it < 0 || allowNotUsingExpect && it == 0,
                    "Expected `finish(${actionIndex.value + 1})` to be called, but the test finished"
                )
            }
        }
    }
}

interface ErrorCatching {
    /**
     * Returns `true` if errors were logged in the test.
     */
    fun hasError(): Boolean

    /**
     * Directly reports an error to the test catching facilities.
     */
    fun reportError(error: Throwable)

    class Impl : ErrorCatching {

        private val errors = mutableListOf<Throwable>()
        private val lock = SynchronizedObject()
        private var closed = false

        override fun hasError(): Boolean = synchronized(lock) {
            errors.isNotEmpty()
        }

        override fun reportError(error: Throwable) {
            synchronized(lock) {
                if (closed) {
                    lastResortReportException(error)
                } else {
                    errors.add(error)
                }
            }
        }

        fun close() {
            synchronized(lock) {
                if (closed) {
                    lastResortReportException(IllegalStateException("ErrorCatching closed more than once"))
                }
                closed = true
                errors.firstOrNull()?.let {
                    for (error in errors.drop(1))
                        it.addSuppressed(error)
                    throw it
                }
            }
        }
    }
}

/**
 * Reports an error *somehow* so that it doesn't get completely forgotten.
 */
internal expect fun lastResortReportException(error: Throwable)

/**
 * Throws [IllegalStateException] when `value` is false, like `check` in stdlib, but also ensures that the
 * test will not complete successfully even if this exception is consumed somewhere in the test.
 */
public inline fun ErrorCatching.check(value: Boolean, lazyMessage: () -> Any) {
    if (!value) error(lazyMessage())
}

/**
 * Throws [IllegalStateException], like `error` in stdlib, but also ensures that the test will not
 * complete successfully even if this exception is consumed somewhere in the test.
 */
fun ErrorCatching.error(message: Any, cause: Throwable? = null): Nothing {
    throw IllegalStateException(message.toString(), cause).also {
        reportError(it)
    }
}

/**
 * A class inheriting from which allows to check the execution order inside tests.
 *
 * @see TestBase
 */
open class OrderedExecutionTestBase : OrderedExecution
{
    // TODO: move to by-delegation when [reset] is no longer needed.
    private var orderedExecutionDelegate = OrderedExecution.Impl()

    @AfterTest
    fun checkFinished() { orderedExecutionDelegate.checkFinishCall() }

    /** Resets counter and finish flag. Workaround for parametrized tests absence in common */
    public fun reset() {
        orderedExecutionDelegate.checkFinishCall()
        orderedExecutionDelegate = OrderedExecution.Impl()
    }

    override fun expect(index: Int) = orderedExecutionDelegate.expect(index)

    override fun finish(index: Int) = orderedExecutionDelegate.finish(index)

    override fun expectUnreached() = orderedExecutionDelegate.expectUnreached()

    override fun checkFinishCall(allowNotUsingExpect: Boolean) =
        orderedExecutionDelegate.checkFinishCall(allowNotUsingExpect)
}

fun <T> T.void() {}

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

public expect open class TestBase(): OrderedExecutionTestBase, ErrorCatching {
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

suspend inline fun <reified T : Throwable> assertFailsWith(flow: Flow<*>) = assertFailsWith<T> { flow.collect() }

public suspend fun Flow<Int>.sum() = fold(0) { acc, value -> acc + value }
public suspend fun Flow<Long>.longSum() = fold(0L) { acc, value -> acc + value }

// data is added to avoid stacktrace recovery because CopyableThrowable is not accessible from common modules
public class TestException(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestException1(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestException2(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestException3(message: String? = null, private val data: Any? = null) : Throwable(message)
public class TestCancellationException(message: String? = null, private val data: Any? = null) :
    CancellationException(message)

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

public expect val isNative: Boolean

/*
 * In common tests we emulate parameterized tests
 * by iterating over parameters space in the single @Test method.
 * This kind of tests is too slow for JS and does not fit into
 * the default Mocha timeout, so we're using this flag to bail-out
 * and run such tests only on JVM and K/N.
 */
public expect val isBoundByJsTestTimeout: Boolean
