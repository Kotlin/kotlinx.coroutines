/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class UnconfinedTest : TestBase() {

    @Test
    fun testOrder() = runTest {
        expect(1)
        launch(Dispatchers.Unconfined) {
            expect(2)
            launch {
                expect(4)
                launch {
                    expect(7)
                }

                launch {
                    expect(6)
                }
                expect(5)
            }

            expect(3)
        }

        finish(8)
    }

    @Test
    fun testBlockThrows() = runTest {
        expect(1)
        try {
            withContext(Dispatchers.Unconfined) {
                expect(2)
                withContext(Dispatchers.Unconfined + CoroutineName("a")) {
                    expect(3)
                }

                expect(4)
                launch(start = CoroutineStart.ATOMIC) {
                    expect(5)
                }

                throw TestException()
            }
        } catch (e: TestException) {
            finish(6)
        }
    }

    @Test
    fun enterMultipleTimes() = runTest {
        launch(Unconfined) {
            expect(1)
        }

        launch(Unconfined) {
            expect(2)
        }

        launch(Unconfined) {
            expect(3)
        }

        finish(4)
    }

    class TestException : Throwable()
}
