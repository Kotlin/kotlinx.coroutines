/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import kotlin.test.*

class RunBlockingTestOrderTest : TestBase() {

    @get:Rule
    val timeout = Timeout.seconds(1)

    @Test
    fun testImmediateExecution() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
        }
        finish(3)
    }

    @Test
    fun testImmediateNestedExecution() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
            launch {
                expect(3)
            }
        }
        finish(4)
    }

    @Test
    fun testExecutionOrder() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
            launch {
                expect(3)
                yield()
                expect(6)
            }
            expect(4)
            yield()
            finish(7)
        }
        expect(5)
    }

    @Test
    fun testDelayInteraction() = runBlockingTest {
        expect(1)
        val result = async {
            expect(2)
            delay(1)
            expect(4)
            42
        }
        expect(3)
        assertEquals(42, result.await())
        finish(5)
    }

}
