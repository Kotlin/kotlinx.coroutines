package kotlinx.coroutines.debug

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class CoroutinesDumpTest : DebugTestBase() {
    private val monitor = Any()
    private var coroutineThread: Thread? = null // guarded by monitor

    @Before
    override fun setUp() {
        super.setUp()
        DebugProbes.enableCreationStackTraces = true
    }

    @Test
    fun testSuspendedCoroutine() = runBlocking {
        val deferred = async(Dispatchers.Default) {
            sleepingOuterMethod()
        }

        awaitCoroutine()
        val found = DebugProbes.dumpCoroutinesInfo().single { it.job === deferred }
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: SUSPENDED\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.sleepingNestedMethod(CoroutinesDumpTest.kt)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.sleepingOuterMethod(CoroutinesDumpTest.kt)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt)\n" +
                    "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt)\n" +
                    "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt)\n",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            deferred.cancel()
            coroutineThread!!.interrupt()
        }
        assertSame(deferred, found.job)
    }

    @Test
    fun testRunningCoroutine() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = false)
            assertTrue(true)
        }

        awaitCoroutine()
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@227d9994, state: RUNNING\n" +
                    "\tat java.lang.Thread.sleep(Native Method)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.nestedActiveMethod(CoroutinesDumpTest.kt)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.activeMethod(CoroutinesDumpTest.kt)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.access\$activeMethod(CoroutinesDumpTest.kt)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest\$testRunningCoroutine\$1\$deferred\$1.invokeSuspend(CoroutinesDumpTest.kt)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt)\n" +
                    "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt)\n" +
                    "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt)\n" +
                    "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest\$testRunningCoroutine\$1.invokeSuspend(CoroutinesDumpTest.kt)",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            deferred.cancel()
            coroutineThread?.interrupt()
        }
    }

    @Test
    fun testRunningCoroutineWithSuspensionPoint() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = true)
            yield() // tail-call
        }

        awaitCoroutine()
        verifyDump(
            "Coroutine \"coroutine#1\":DeferredCoroutine{Active}@1e4a7dd4, state: RUNNING\n" +
                    "\tat java.lang.Thread.sleep(Native Method)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.nestedActiveMethod(CoroutinesDumpTest.kt)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest.activeMethod(CoroutinesDumpTest.kt)\n" +
                    "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                    "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt)\n" +
                    "\tat kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt)\n" +
                    "\tat kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt)\n" +
                    "\tat kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.debug.CoroutinesDumpTest\$testRunningCoroutineWithSuspensionPoint\$1.invokeSuspend(CoroutinesDumpTest.kt)",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            deferred.cancel()
            coroutineThread!!.interrupt()
        }
    }

    /**
     * Tests that a coroutine started with [CoroutineStart.UNDISPATCHED] is considered running.
     */
    @Test
    fun testUndispatchedCoroutineIsRunning() = runBlocking {
        val job = launch(Dispatchers.IO, start = CoroutineStart.UNDISPATCHED) { // or launch(Dispatchers.Unconfined)
            verifyDump(
                "Coroutine \"coroutine#1\":StandaloneCoroutine{Active}@1e4a7dd4, state: RUNNING\n",
                ignoredCoroutine = "BlockingCoroutine"
            )
            delay(Long.MAX_VALUE)
        }
        verifyDump(
            "Coroutine \"coroutine#1\":StandaloneCoroutine{Active}@1e4a7dd4, state: SUSPENDED\n",
            ignoredCoroutine = "BlockingCoroutine"
        ) {
            job.cancel()
        }
    }

    @Test
    fun testCreationStackTrace() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutine()
        val coroutine = DebugProbes.dumpCoroutinesInfo().first { it.job is Deferred<*> }
        val result = coroutine.creationStackTrace.fold(StringBuilder()) { acc, element ->
            acc.append(element.toString())
            acc.append('\n')
        }.toString().trimStackTrace()

        deferred.cancel()
        coroutineThread!!.interrupt()

        val expected =
            "kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt)\n" +
            "kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt)\n" +
            "kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt)\n" +
            "kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt)\n" +
            "kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt)\n" +
            "kotlinx.coroutines.BuildersKt.async(Unknown Source)\n" +
            "kotlinx.coroutines.BuildersKt__Builders_commonKt.async\$default(Builders.common.kt)\n" +
            "kotlinx.coroutines.BuildersKt.async\$default(Unknown Source)\n" +
            "kotlinx.coroutines.debug.CoroutinesDumpTest\$testCreationStackTrace\$1.invokeSuspend(CoroutinesDumpTest.kt)"
        if (!result.startsWith(expected)) {
            error("""
                |Does not start with expected lines
                |=== Actual result:
                |$result
                """.trimMargin()
            )
        }

    }

    @Test
    fun testFinishedCoroutineRemoved() = runBlocking {
        val deferred = async(Dispatchers.IO) {
            activeMethod(shouldSuspend = true)
        }

        awaitCoroutine()
        deferred.cancel()
        coroutineThread!!.interrupt()
        deferred.join()
        verifyDump(ignoredCoroutine = "BlockingCoroutine")
    }

    private suspend fun activeMethod(shouldSuspend: Boolean) {
        nestedActiveMethod(shouldSuspend)
        assertTrue(true) // tail-call
    }

    private suspend fun nestedActiveMethod(shouldSuspend: Boolean) {
        if (shouldSuspend) yield()
        notifyCoroutineStarted()
        while (coroutineContext[Job]!!.isActive) {
            try {
                Thread.sleep(60_000)
            } catch (_ : InterruptedException) {
            }
        }
    }

    private suspend fun sleepingOuterMethod() {
        sleepingNestedMethod()
        yield() // TCE
    }

    private suspend fun sleepingNestedMethod() {
        yield() // Suspension point
        notifyCoroutineStarted()
        delay(Long.MAX_VALUE)
    }

    private fun awaitCoroutine() = synchronized(monitor) {
        while (coroutineThread == null) (monitor as Object).wait()
        while (coroutineThread!!.state != Thread.State.TIMED_WAITING) {
            // Wait until thread sleeps to have a consistent stacktrace
        }
    }

    private fun notifyCoroutineStarted() {
        synchronized(monitor) {
            coroutineThread = Thread.currentThread()
            (monitor as Object).notifyAll()
        }
    }
}
