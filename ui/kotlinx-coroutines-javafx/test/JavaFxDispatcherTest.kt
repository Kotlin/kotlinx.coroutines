/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.javafx

import javafx.application.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class JavaFxDispatcherTest : TestBase() {
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

    @Test
    fun testImmediateDispatcherYield() {
        if (!initPlatform()) {
            println("Skipping JavaFxTest in headless environment")
            return // ignore test in headless environments
        }

        runBlocking(Dispatchers.JavaFx) {
            expect(1)
            check(Platform.isFxApplicationThread())
            // launch in the immediate dispatcher
            launch(Dispatchers.JavaFx.immediate) {
                expect(2)
                yield()
                expect(4)
            }
            expect(3) // after yield
            yield() // yield back
            finish(5)
        }
    }

    @Test
    fun testMainDispatcherToString() {
        assertEquals("Dispatchers.Main", Dispatchers.Main.toString())
        assertEquals("Dispatchers.Main.immediate", Dispatchers.Main.immediate.toString())
    }
}