/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.swing

import kotlinx.coroutines.*
import org.junit.*
import javax.swing.*

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
}