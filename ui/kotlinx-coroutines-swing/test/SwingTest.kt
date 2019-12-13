/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.swing

import javafx.application.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import javax.swing.*
import kotlin.coroutines.*
import kotlin.test.*

class SwingTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("AWT-EventQueue-")
    }

    @Test
    fun testDelay() = runBlocking {
        expect(1)
        SwingUtilities.invokeLater { expect(2) }
        val job = launch(Dispatchers.Swing) {
            check(SwingUtilities.isEventDispatchThread())
            expect(3)
            SwingUtilities.invokeLater { expect(4) }
            delay(100)
            check(SwingUtilities.isEventDispatchThread())
            expect(5)
        }
        job.join()
        finish(6)
    }

    private class SwingComponent(coroutineContext: CoroutineContext = EmptyCoroutineContext) :
        CoroutineScope by MainScope() + coroutineContext
    {
        public var executed = false
        fun testLaunch(): Job = launch {
            check(SwingUtilities.isEventDispatchThread())
            executed = true
        }
        fun testFailure(): Job = launch {
            check(SwingUtilities.isEventDispatchThread())
            throw TestException()
        }
        fun testCancellation() : Job = launch(start = CoroutineStart.ATOMIC) {
            check(SwingUtilities.isEventDispatchThread())
            delay(Long.MAX_VALUE)
        }
    }

    @Test
    fun testLaunchInMainScope() = runTest {
        val component = SwingComponent()
        val job = component.testLaunch()
        job.join()
        assertTrue(component.executed)
        component.cancel()
        component.coroutineContext[Job]!!.join()
    }

    @Test
    fun testFailureInMainScope() = runTest {
        var exception: Throwable? = null
        val component = SwingComponent(CoroutineExceptionHandler { ctx, e ->  exception = e})
        val job = component.testFailure()
        job.join()
        assertTrue(exception!! is TestException)
        component.cancel()
        join(component)
    }

    @Test
    fun testCancellationInMainScope() = runTest {
        val component = SwingComponent()
        component.cancel()
        component.testCancellation().join()
        join(component)
    }

    private suspend fun join(component: SwingTest.SwingComponent) {
        component.coroutineContext[Job]!!.join()
    }

    @Test
    fun testImmediateDispatcherYield() = runBlocking(Dispatchers.Swing) {
        expect(1)
        // launch in the immediate dispatcher
        launch(Dispatchers.Swing.immediate) {
            expect(2)
            yield()
            expect(4)
        }
        expect(3) // after yield
        yield() // yield back
        finish(5)
    }
}