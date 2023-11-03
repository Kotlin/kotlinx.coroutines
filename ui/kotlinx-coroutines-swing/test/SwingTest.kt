/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.swing

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import javax.swing.*
import kotlin.coroutines.*
import kotlin.test.*

class SwingTest : MainDispatcherTestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("AWT-EventQueue-")
    }

    override fun checkIsMainThread() { check(SwingUtilities.isEventDispatchThread()) }


    /** Tests that the Main dispatcher is in fact the JavaFx one. */
    @Test
    fun testMainIsJavaFx() {
        assertSame(Dispatchers.Swing, Dispatchers.Main)
    }

    /** similar to [MainDispatcherTestBase.testDelay], but also uses `invokeLater` */
    @Test
    fun testDelayWithInvokeLater() = runBlocking {
        expect(1)
        SwingUtilities.invokeLater { expect(2) }
        val job = launch(Dispatchers.Main) {
            checkIsMainThread()
            expect(3)
            SwingUtilities.invokeLater { expect(4) }
            delay(100)
            checkIsMainThread()
            expect(5)
        }
        job.join()
        finish(6)
    }
}
