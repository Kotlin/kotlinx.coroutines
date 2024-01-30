package kotlinx.coroutines.testing

import kotlinx.coroutines.scheduling.*
import java.io.*
import java.util.*
import kotlin.coroutines.*
import kotlinx.coroutines.*
import kotlin.test.*

actual val VERBOSE = try {
    System.getProperty("test.verbose")?.toBoolean() ?: false
} catch (e: SecurityException) {
    false
}

/**
 * Is `true` when running in a nightly stress test mode.
 */
actual val isStressTest = System.getProperty("stressTest")?.toBoolean() ?: false

actual val stressTestMultiplierSqrt = if (isStressTest) 5 else 1

private const val SHUTDOWN_TIMEOUT = 1_000L // 1s at most to wait per thread

/**
 * Multiply various constants in stress tests by this factor, so that they run longer during nightly stress test.
 */
actual val stressTestMultiplier = stressTestMultiplierSqrt * stressTestMultiplierSqrt


@Suppress("ACTUAL_WITHOUT_EXPECT")
actual typealias TestResult = Unit

internal actual fun lastResortReportException(error: Throwable) {
    System.err.println("${error.message}${error.cause?.let { ": $it" } ?: ""}")
    error.cause?.printStackTrace(System.err)
    System.err.println("--- Detected at ---")
    Throwable().printStackTrace(System.err)
}

/**
 * Base class for tests, so that tests for predictable scheduling of actions in multiple coroutines sharing a single
 * thread can be written. Use it like this:
 *
 * ```
 * class MyTest : TestBase() {
 *    @Test
 *    fun testSomething() = runBlocking { // run in the context of the main thread
 *        expect(1) // initiate action counter
 *        launch { // use the context of the main thread
 *           expect(3) // the body of this coroutine in going to be executed in the 3rd step
 *        }
 *        expect(2) // launch just scheduled coroutine for execution later, so this line is executed second
 *        yield() // yield main thread to the launched job
 *        finish(4) // fourth step is the last one. `finish` must be invoked or test fails
 *    }
 * }
 * ```
 */
actual open class TestBase(
    private var disableOutCheck: Boolean,
    private val errorCatching: ErrorCatching.Impl = ErrorCatching.Impl()
): OrderedExecutionTestBase(), ErrorCatching by errorCatching {

    actual constructor(): this(false)

    // Shutdown sequence
    private lateinit var threadsBefore: Set<Thread>
    private val uncaughtExceptions = Collections.synchronizedList(ArrayList<Throwable>())
    private var originalUncaughtExceptionHandler: Thread.UncaughtExceptionHandler? = null
    /*
     * System.out that we redefine in order to catch any debugging/diagnostics
     * 'println' from main source set.
     * NB: We do rely on the name 'previousOut' in the FieldWalker in order to skip its
     * processing
     */
    private lateinit var previousOut: PrintStream

    private object TestOutputStream : PrintStream(object : OutputStream() {
        override fun write(b: Int) {
            error("Detected unexpected call to 'println' from source code")
        }
    })

    actual fun println(message: Any?) {
        if (disableOutCheck) kotlin.io.println(message)
        else previousOut.println(message)
    }

    @BeforeTest
    fun before() {
        initPoolsBeforeTest()
        threadsBefore = currentThreads()
        originalUncaughtExceptionHandler = Thread.getDefaultUncaughtExceptionHandler()
        Thread.setDefaultUncaughtExceptionHandler { t, e ->
            println("Exception in thread $t: $e") // The same message as in default handler
            e.printStackTrace()
            uncaughtExceptions.add(e)
        }
        if (!disableOutCheck) {
            previousOut = System.out
            System.setOut(TestOutputStream)
        }
    }

    @AfterTest
    fun onCompletion() {
        // onCompletion should not throw exceptions before it finishes all cleanup, so that other tests always
        // start in a clear, restored state
        checkFinishCall()
        if (!disableOutCheck) { // Restore global System.out first
            System.setOut(previousOut)
        }
        // Shutdown all thread pools
        shutdownPoolsAfterTest()
        // Check that are now leftover threads
        runCatching {
            checkTestThreads(threadsBefore)
        }.onFailure {
            reportError(it)
        }
        // Restore original uncaught exception handler after the main shutdown sequence
        Thread.setDefaultUncaughtExceptionHandler(originalUncaughtExceptionHandler)
        if (uncaughtExceptions.isNotEmpty()) {
            error("Expected no uncaught exceptions, but got $uncaughtExceptions")
        }
        // The very last action -- throw error if any was detected
        errorCatching.close()
    }

    actual fun runTest(
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
            } else {
                throw e
            }
        } finally {
            if (ex == null && expected != null) error("Exception was expected but none produced")
        }
        if (exCount < unhandled.size)
            error("Too few unhandled exceptions $exCount, expected ${unhandled.size}")
    }

    protected suspend fun currentDispatcher() = coroutineContext[ContinuationInterceptor]!!
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
fun initPoolsBeforeTest() {
    DefaultScheduler.usePrivateScheduler()
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
fun shutdownPoolsAfterTest() {
    DefaultScheduler.shutdown(SHUTDOWN_TIMEOUT)
    DefaultExecutor.shutdownForTests(SHUTDOWN_TIMEOUT)
    DefaultScheduler.restore()
}

actual val isNative = false

actual val isBoundByJsTestTimeout = false

/*
 * We ignore tests that test **real** non-virtualized tests with time on Windows, because
 * our CI Windows is virtualized itself (oh, the irony) and its clock resolution is dozens of ms,
 * which makes such tests flaky.
 */
actual val isJavaAndWindows: Boolean = System.getProperty("os.name")!!.contains("Windows")
