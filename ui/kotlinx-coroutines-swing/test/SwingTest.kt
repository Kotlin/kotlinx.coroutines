/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.swing

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.Test
import javax.swing.*
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
        val job = launch(Swing) {
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

    @Test
    fun testRunBlockingForbidden() {
        runBlocking(Swing) {
            expect(1)
            try {
                runBlocking(Swing) {
                    expectUnreached()
                }
            } catch (e: IllegalStateException) {
                assertTrue(e.message!!.contains("runBlocking"))
                finish(2)
            }
        }
    }
}
