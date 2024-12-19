package kotlinx.coroutines.testing

import kotlin.test.*
import kotlinx.coroutines.*
import kotlinx.coroutines.scheduling.*

actual val VERBOSE = false

actual typealias NoNative = Ignore

public actual val isStressTest: Boolean = false
public actual val stressTestMultiplier: Int = 1
public actual val stressTestMultiplierSqrt: Int = 1

private const val SHUTDOWN_TIMEOUT = 1_000L // 1s at most to wait per thread

@Suppress("ACTUAL_WITHOUT_EXPECT")
public actual typealias TestResult = Unit

internal actual fun lastResortReportException(error: Throwable) {
    println(error)
}

public actual open class TestBase actual constructor(): OrderedExecutionTestBase(), ErrorCatching by ErrorCatching.Impl() {
    actual fun println(message: Any?) {
        kotlin.io.println(message)
    }

    public actual fun runTest(
        expected: ((Throwable) -> Boolean)?,
        unhandled: List<(Throwable) -> Boolean>,
        block: suspend CoroutineScope.() -> Unit
    ): TestResult {
        var exCount = 0
        var ex: Throwable? = null
        try {
            runBlocking(block = block, context = CoroutineExceptionHandler { _, e ->
                if (e is CancellationException) return@CoroutineExceptionHandler // are ignored
                exCount++
                when {
                    exCount > unhandled.size ->
                        error("Too many unhandled exceptions $exCount, expected ${unhandled.size}, got: $e", e)
                    !unhandled[exCount - 1](e) ->
                        error("Unhandled exception was unexpected: $e", e)
                }
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


    @BeforeTest
    fun before() {
        initPoolsBeforeTest()
    }

    @AfterTest
    fun onCompletion() {
        // Shutdown all thread pools
        shutdownPoolsAfterTest()
    }
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
fun initPoolsBeforeTest() {
    DefaultScheduler.usePrivateScheduler()
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
fun shutdownPoolsAfterTest() {
    DefaultScheduler.shutdown(SHUTDOWN_TIMEOUT)
    DefaultScheduler.restore()
}

public actual val isNative = true

public actual val isBoundByJsTestTimeout = false

public actual val isJavaAndWindows: Boolean get() = false

actual val usesSharedEventLoop: Boolean = false
