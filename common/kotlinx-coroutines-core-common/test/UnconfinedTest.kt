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
                    expect(6)
                }

                launch {
                    expect(7)
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
    fun testEnterMultipleTimes() = runTest {
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

    @Test
    fun testYield() = runTest {
        expect(1)
        launch(Dispatchers.Unconfined) {
            expect(2)
            yield()
            launch {
                expect(4)
            }
            expect(3)
            yield()
            expect(5)
        }.join()

        finish(6)
    }

    @Test
    fun testCancellationWihYields() = runTest {
        expect(1)
        GlobalScope.launch(Dispatchers.Unconfined) {
            val job = coroutineContext[Job]!!
            expect(2)
            yield()
            GlobalScope.launch(Dispatchers.Unconfined) {
                expect(4)
                job.cancel()
                expect(5)
            }
            expect(3)

            try {
                yield()
            } finally {
                expect(6)
            }
        }

        finish(7)
    }

    class TestException : Throwable()
}
