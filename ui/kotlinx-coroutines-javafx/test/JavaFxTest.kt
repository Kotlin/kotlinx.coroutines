/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.javafx

import javafx.application.*
import kotlinx.coroutines.*
import org.junit.*

class JavaFxTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("JavaFX Application Thread", "Thread-", "QuantumRenderer-", "InvokeLaterDispatcher")
    }

    @Test
    fun testDelay() {
        if (!initPlatform()) {
            println("Skipping JavaFxTest in headless environment")
            return // ignore test in headless environments
        }

        runBlocking {
            expect(1)
            val job = launch(Dispatchers.JavaFx) {
                check(Platform.isFxApplicationThread())
                expect(2)
                delay(100)
                check(Platform.isFxApplicationThread())
                expect(3)
            }
            job.join()
            finish(4)
        }
    }
}