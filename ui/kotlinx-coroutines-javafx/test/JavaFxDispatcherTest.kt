/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.javafx

import javafx.application.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import javax.swing.*
import kotlin.test.*

class JavaFxDispatcherTest : MainDispatcherTestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("JavaFX Application Thread", "Thread-", "QuantumRenderer-", "InvokeLaterDispatcher")
    }

    override fun shouldSkipTesting(): Boolean {
        if (!initPlatform()) {
            println("Skipping JavaFxTest in headless environment")
            return true // ignore test in headless environments
        }
        return false
    }

    override fun isMainThread() = Platform.isFxApplicationThread()

    override fun scheduleOnMainQueue(block: () -> Unit) {
        Platform.runLater { block() }
    }

    /** Tests that the Main dispatcher is in fact the JavaFx one. */
    @Test
    fun testMainIsJavaFx() {
        assertSame(Dispatchers.JavaFx, Dispatchers.Main)
    }

}
