/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlin.test.*

class SelectOldTest : TestBase() {
    @Test
    fun testSelectCompleted() = runTest {
        expect(1)
        launch { // makes sure we don't yield to it earlier
            finish(4) // after main exits
        }
        val job = Job()
        job.cancel()
        selectOld<Unit> {
            job.onJoin {
                expect(2)
            }
        }
        expect(3)
        // will wait for the first coroutine
    }

    @Test
    fun testSelectUnbiasedCompleted() = runTest {
        expect(1)
        launch { // makes sure we don't yield to it earlier
            finish(4) // after main exits
        }
        val job = Job()
        job.cancel()
        selectUnbiasedOld<Unit> {
            job.onJoin {
                expect(2)
            }
        }
        expect(3)
        // will wait for the first coroutine
    }

    @Test
    fun testSelectIncomplete() = runTest {
        expect(1)
        val job = Job()
        launch { // makes sure we don't yield to it earlier
            expect(3)
            val res = selectOld<String> {
                job.onJoin {
                    expect(6)
                    "OK"
                }
            }
            expect(7)
            assertEquals("OK", res)
        }
        expect(2)
        yield()
        expect(4)
        job.cancel()
        expect(5)
        yield()
        finish(8)
    }

    @Test
    fun testSelectUnbiasedIncomplete() = runTest {
        expect(1)
        val job = Job()
        launch { // makes sure we don't yield to it earlier
            expect(3)
            val res = selectUnbiasedOld<String> {
                job.onJoin {
                    expect(6)
                    "OK"
                }
            }
            expect(7)
            assertEquals("OK", res)
        }
        expect(2)
        yield()
        expect(4)
        job.cancel()
        expect(5)
        yield()
        finish(8)
    }

    @Test
    fun testSelectUnbiasedComplete() = runTest {
        expect(1)
        val job = Job()
        job.complete()
        expect(2)
        val res = selectUnbiasedOld<String> {
            job.onJoin {
                expect(3)
                "OK"
            }
        }
        assertEquals("OK", res)
        finish(4)
    }

    @Test
    fun testSelectUnbiasedThrows() = runTest {
        try {
            select<Unit> {
                expect(1)
                throw TestException()
            }
        } catch (e: TestException) {
            finish(2)
        }
    }

    @Test
    fun testSelectLazy() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.LAZY) {
            expect(2)
        }
        val res = selectOld<String> {
            job.onJoin {
                expect(3)
                "OK"
            }
        }
        finish(4)
        assertEquals("OK", res)
    }

    @Test
    fun testSelectUnbiasedLazy() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.LAZY) {
            expect(2)
        }
        val res = selectUnbiasedOld<String> {
            job.onJoin {
                expect(3)
                "OK"
            }
        }
        finish(4)
        assertEquals("OK", res)
    }
}
