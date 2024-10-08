package kotlinx.coroutines.debug

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import kotlin.test.*

class StartModeProbesTest : DebugTestBase() {

    @Test
    fun testUndispatched() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            undispatchedSleeping()
            assertTrue(true)
        }

        yield()
        expect(3)
        verifyPartialDump(2, "StartModeProbesTest.undispatchedSleeping")
        job.cancelAndJoin()
        verifyPartialDump(1, "StartModeProbesTest\$testUndispatched")
        finish(4)
    }

    private suspend fun undispatchedSleeping() {
        delay(Long.MAX_VALUE)
        assertTrue(true)
    }

    @Test
    fun testWithTimeoutWithUndispatched() = runTest {
        expect(1)
        val job = launchUndispatched()

        yield()
        expect(3)
        verifyPartialDump(
            2,
            "StartModeProbesTest\$launchUndispatched\$1.invokeSuspend",
            "StartModeProbesTest.withTimeoutHelper",
            "StartModeProbesTest\$withTimeoutHelper\$2.invokeSuspend"
        )
        job.cancelAndJoin()
        verifyPartialDump(1, "StartModeProbesTest\$testWithTimeoutWithUndispatched")
        finish(4)
    }

    private fun CoroutineScope.launchUndispatched(): Job {
        return launch(start = CoroutineStart.UNDISPATCHED) {
            withTimeoutHelper()
            assertTrue(true)
        }
    }

    private suspend fun withTimeoutHelper() {
        withTimeout(Long.MAX_VALUE) {
            expect(2)
            delay(Long.MAX_VALUE)
        }

        assertTrue(true)
    }

    @Test
    fun testWithTimeout() = runTest {
        withTimeout(Long.MAX_VALUE) {
            testActiveDump(
                false,
                "StartModeProbesTest\$testWithTimeout\$1.invokeSuspend",
                "state: RUNNING"
            )
        }
    }

    @Test
    fun testWithTimeoutAfterYield() = runTest {
        withTimeout(Long.MAX_VALUE) {
            testActiveDump(
                true,
                "StartModeProbesTest\$testWithTimeoutAfterYield\$1.invokeSuspend",
                "StartModeProbesTest\$testWithTimeoutAfterYield\$1\$1.invokeSuspend",
                "StartModeProbesTest.testActiveDump",
                "state: RUNNING"
            )
        }
    }

    private suspend fun testActiveDump(shouldYield: Boolean, vararg expectedFrames: String) {
        if (shouldYield) yield()
        verifyPartialDump(1, *expectedFrames)
        assertTrue(true)
    }

    @Test
    fun testWithTailCall() = runTest {
        expect(1)
        val job = tailCallMethod()
        yield()
        expect(3)
        verifyPartialDump(2, "StartModeProbesTest\$launchFromTailCall\$2")
        job.cancelAndJoin()
        verifyPartialDump(1, "StartModeProbesTest\$testWithTailCall")
        finish(4)
    }

    private suspend fun CoroutineScope.tailCallMethod(): Job = launchFromTailCall()
    private suspend fun CoroutineScope.launchFromTailCall(): Job = launch {
        expect(2)
        delay(Long.MAX_VALUE)
    }

    @Test
    fun testCoroutineScope() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            runScope()
        }

        yield()
        expect(3)
        verifyPartialDump(
            2,
            "StartModeProbesTest\$runScope\$2.invokeSuspend",
            "StartModeProbesTest\$testCoroutineScope\$1\$job\$1.invokeSuspend")
        job.cancelAndJoin()
        finish(4)
    }

    private suspend fun runScope() {
        coroutineScope {
            expect(2)
            delay(Long.MAX_VALUE)
        }
    }

    @Test
    fun testLazy() = runTest({ it is CancellationException }) {
        launch(start = CoroutineStart.LAZY) {  }
        actor<Int>(start = CoroutineStart.LAZY) {  }
        @Suppress("DEPRECATION_ERROR")
        broadcast<Int>(start = CoroutineStart.LAZY) {  }
        async(start = CoroutineStart.LAZY) { 1 }
        verifyPartialDump(5, "BlockingCoroutine",
            "LazyStandaloneCoroutine", "LazyActorCoroutine",
            "LazyBroadcastCoroutine", "LazyDeferredCoroutine")
        cancel()
    }
}
