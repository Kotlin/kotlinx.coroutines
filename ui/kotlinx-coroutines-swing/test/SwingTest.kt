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

    override fun isMainThread() = SwingUtilities.isEventDispatchThread()

    override fun scheduleOnMainQueue(block: () -> Unit) {
        SwingUtilities.invokeLater { block() }
    }

    /** Tests that the Main dispatcher is in fact the JavaFx one. */
    @Test
    fun testMainIsJavaFx() {
        assertSame(Dispatchers.Swing, Dispatchers.Main)
    }
}
