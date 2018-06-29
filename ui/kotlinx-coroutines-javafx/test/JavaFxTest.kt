/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.javafx

import javafx.application.Platform
import kotlinx.coroutines.experimental.*
import org.junit.Before
import org.junit.Test

class JavaFxTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("JavaFX Application Thread", "Thread-", "QuantumRenderer-")
    }

    @Test
    fun testDelay() {
        try {
            initPlatform()
        } catch (e: UnsupportedOperationException) {
            println("Skipping JavaFxTest in headless environment")
            return // ignore test in headless environments
        }

        runBlocking {
            expect(1)
            val job = launch(JavaFx) {
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