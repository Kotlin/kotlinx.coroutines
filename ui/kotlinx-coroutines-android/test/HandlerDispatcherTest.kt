package kotlinx.coroutines.android

import kotlinx.coroutines.testing.*
import android.os.*
import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import org.junit.Test
import org.junit.runner.*
import org.robolectric.*
import org.robolectric.annotation.*
import org.robolectric.shadows.*
import java.util.concurrent.*
import kotlin.test.*

@RunWith(RobolectricTestRunner::class)
@LooperMode(LooperMode.Mode.LEGACY)
@Config(manifest = Config.NONE, sdk = [28])
class HandlerDispatcherTest : MainDispatcherTestBase.WithRealTimeDelay() {
    @Test
    fun testDefaultDelayIsNotDelegatedToMain() = runTest {
        val mainLooper = Shadows.shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        assertFalse { mainLooper.scheduler.areAnyRunnable() }

        val job = launch(Dispatchers.Default, start = CoroutineStart.UNDISPATCHED) {
            expect(1)
            delay(Long.MAX_VALUE)
            expectUnreached()
        }
        expect(2)
        assertEquals(0, mainLooper.scheduler.size())
        job.cancelAndJoin()
        finish(3)
    }

    @Test
    fun testWithTimeoutIsDelegatedToMain() = runTest {
        val mainLooper = Shadows.shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        assertFalse { mainLooper.scheduler.areAnyRunnable() }
        val job = launch(Dispatchers.Main, start = CoroutineStart.UNDISPATCHED) {
            withTimeout(1) {
                expect(1)
                hang { expect(3) }
            }
            expectUnreached()
        }
        expect(2)
        assertEquals(1, mainLooper.scheduler.size())
        // Schedule cancellation
        mainLooper.runToEndOfTasks()
        job.join()
        finish(4)
    }

    @Test
    fun testDelayDelegatedToMain() = runTest {
        val mainLooper = Shadows.shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        val job = launch(Dispatchers.Main, start = CoroutineStart.UNDISPATCHED) {
            expect(1)
            delay(1)
            expect(3)
        }
        expect(2)
        assertEquals(1, mainLooper.scheduler.size())
        // Schedule cancellation
        mainLooper.runToEndOfTasks()
        job.join()
        finish(4)
    }

    @Test
    fun testAwaitFrame() = runTest {
        doTestAwaitFrame()

        reset()

        // Now the second test: we cannot test it separately because we're caching choreographer in HandlerDispatcher
        doTestAwaitWithDetectedChoreographer()
    }

    private fun CoroutineScope.doTestAwaitFrame() {
        ShadowChoreographer.setPostFrameCallbackDelay(100)
        val mainLooper = Shadows.shadowOf(Looper.getMainLooper())
        mainLooper.pause()
        launch(Dispatchers.Main, start = CoroutineStart.UNDISPATCHED) {
            expect(1)
            awaitFrame()
            expect(3)
        }
        expect(2)
        // Run choreographer detection
        mainLooper.runOneTask()
        finish(4)
    }

    private fun CoroutineScope.doTestAwaitWithDetectedChoreographer() {
        ShadowChoreographer.setPostFrameCallbackDelay(100)
        val mainLooper = Shadows.shadowOf(Looper.getMainLooper())
        launch(Dispatchers.Main, start = CoroutineStart.UNDISPATCHED) {
            expect(1)
            awaitFrame()
            expect(4)
        }
        // Run choreographer detection
        expect(2)
        mainLooper.scheduler.advanceBy(50, TimeUnit.MILLISECONDS)
        expect(3)
        mainLooper.scheduler.advanceBy(51, TimeUnit.MILLISECONDS)
        finish(5)
    }

    override fun isMainThread(): Boolean = Looper.getMainLooper().thread === Thread.currentThread()

    override fun scheduleOnMainQueue(block: () -> Unit) {
        Handler(Looper.getMainLooper()).post(block)
    }

    // by default, Robolectric only schedules tasks on the main thread but doesn't run them.
    // This function nudges it to run them, 10 milliseconds of virtual time at a time.
    override suspend fun spinTest(testBody: Job) {
        val mainLooper = Shadows.shadowOf(Looper.getMainLooper())
        while (testBody.isActive) {
            Thread.sleep(10, 0)
            mainLooper.idleFor(10, TimeUnit.MILLISECONDS)
        }
    }
}
