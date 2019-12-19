/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.swt

import kotlinx.coroutines.*
import org.eclipse.swt.widgets.Display
import org.junit.AfterClass
import org.junit.Before
import org.junit.BeforeClass
import org.junit.Test
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.assertTrue

class SwtTest : TestBase() {

    private val display
        get() = DISPATCHER.display

    @Before
    fun setup() {
        ignoreLostThreads(DISPATCHER.name)
    }

    @Test
    fun testDelay() = runBlocking(Dispatchers.IO) {
        check(!display.isEventDispatchThread())

        expect(1)
        display.asyncExec { expect(2) }
        val job = launch(Dispatchers.SWT) {
            check(display.isEventDispatchThread())
            expect(3)
            display.asyncExec { expect(4) }
            delay(100)
            check(display.isEventDispatchThread())
            expect(5)
        }

        job.join()
        finish(6)
    }

    @Test
    fun testLaunchInMainScope() = runTest {
        check(!display.isEventDispatchThread())

        val component = SwtComponent(display)
        val job = component.testLaunch()

        job.join()

        assertTrue(component.executed)
        component.cancel()
        component.coroutineContext[Job]!!.join()
    }

    @Test
    fun testFailureInMainScope() = runTest {
        check(!display.isEventDispatchThread())

        var exception: Throwable? = null
        val component = SwtComponent(display, CoroutineExceptionHandler { _, e -> exception = e })
        val job = component.testFailure()

        job.join()

        assertTrue(exception is TestException)
        component.cancel()
        join(component)
    }

    @Test
    fun testCancellationInMainScope() = runTest {
        check(!display.isEventDispatchThread())

        val component = SwtComponent(display)
        component.cancel()
        component.testCancellation().join()
        join(component)
    }

    @Test
    fun testImmediateDispatcherYield() = runBlocking(Dispatchers.SWT) {
        expect(1)
        // launch in the immediate dispatcher
        launch(Dispatchers.SWT.immediate) {
            expect(2)
            yield()
            expect(4)
        }
        expect(3) // after yield
        yield() // yield back
        finish(5)
    }

    private suspend fun join(component: SwtComponent) {
        component.coroutineContext[Job]!!.join()
    }

    private class SwtComponent(
            private val display: Display,
            coroutineContext: CoroutineContext = EmptyCoroutineContext
    ) : CoroutineScope by MainScope() + coroutineContext {

        var executed = false

        fun testLaunch(): Job = launch {
            check(display.isEventDispatchThread())
            executed = true
        }

        fun testFailure(): Job = launch {
            check(display.isEventDispatchThread())
            throw TestException()
        }

        fun testCancellation(): Job = launch(start = CoroutineStart.ATOMIC) {
            check(display.isEventDispatchThread())
            delay(Long.MAX_VALUE)
        }
    }

    companion object {

        private lateinit var DISPATCHER: SWTDefaultDisplayDispatchThread

        @BeforeClass
        @JvmStatic
        fun init() {
            DISPATCHER = SWTDefaultDisplayDispatchThread()
        }

        @AfterClass
        @JvmStatic
        fun cleanup() {
            DISPATCHER.dispose()
        }
    }
}

private fun Display.isEventDispatchThread() = thread == Thread.currentThread()
