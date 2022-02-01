/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import android.os.*
import kotlinx.coroutines.*
import org.junit.Test
import org.junit.runner.*
import org.robolectric.*
import org.robolectric.annotation.*
import org.robolectric.shadows.*
import java.util.concurrent.*
import kotlin.test.*

@RunWith(RobolectricTestRunner::class)
@Config(manifest = Config.NONE, sdk = [28])
class HandlerDispatcherTest : TestBase() {
    @Test
    fun testImmediateDispatcherYield() = runBlocking(Dispatchers.Main) {
        expect(1)
        // launch in the immediate dispatcher
        launch(Dispatchers.Main.immediate) {
            expect(2)
            yield()
            expect(4)
        }
        expect(3) // after yield
        yield() // yield back
        finish(5)
    }

    @Test
    fun testMainDispatcherToString() {
        assertEquals("Dispatchers.Main", Dispatchers.Main.toString())
        assertEquals("Dispatchers.Main.immediate", Dispatchers.Main.immediate.toString())
    }

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
            expect(5)
        }
        expect(2)
        // Run choreographer detection
        mainLooper.runOneTask()
        expect(3)
        mainLooper.scheduler.advanceBy(50, TimeUnit.MILLISECONDS)
        expect(4)
        mainLooper.scheduler.advanceBy(51, TimeUnit.MILLISECONDS)
        finish(6)
    }

    private fun CoroutineScope.doTestAwaitWithDetectedChoreographer() {
        ShadowChoreographer.reset()
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
}
