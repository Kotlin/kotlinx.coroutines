/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class SupervisorTest : TestBase() {
    @Test
    fun testSupervisorJob() = runTest(
        unhandled = listOf(
            { it -> it is TestException2 },
            { it -> it is TestException1 }
        )
    ) {
        expect(1)
        val supervisor = SupervisorJob()
        val job1 = launch(supervisor + CoroutineName("job1")) {
            expect(2)
            yield() // to second child
            expect(4)
            throw TestException1()
        }
        val job2 = launch(supervisor + CoroutineName("job2")) {
            expect(3)
            throw TestException2()
        }
        joinAll(job1, job2)
        finish(5)
        assertTrue(job1.isCancelled)
        assertTrue(job2.isCancelled)
        assertFalse(supervisor.isCancelled)
        assertFalse(supervisor.isCompleted)
    }

    @Test
    fun testSupervisorScope() = runTest(
        unhandled = listOf(
            { it -> it is TestException1 },
            { it -> it is TestException2 }
        )
    ) {
        val result = supervisorScope {
            launch {
                throw TestException1()
            }
            launch {
                throw TestException2()
            }
            "OK"
        }
        assertEquals("OK", result)
    }

    @Test
    fun testSupervisorScopeIsolation() = runTest(
        unhandled = listOf(
            { it -> it is TestException2 })
    ) {
        val result = supervisorScope {
            expect(1)
            val job = launch {
                expect(2)
                delay(Long.MAX_VALUE)
            }

            val failingJob = launch {
                expect(3)
                throw TestException2()
            }

            failingJob.join()
            yield()
            expect(4)
            assertTrue(job.isActive)
            assertFalse(job.isCancelled)
            job.cancel()
            "OK"
        }
        assertEquals("OK", result)
        finish(5)
    }

    @Test
    fun testThrowingSupervisorScope() = runTest {
        try {
            expect(1)
            supervisorScope {
                async {
                    try {
                        delay(Long.MAX_VALUE)
                    } finally {
                        expect(3)
                    }
                }

                expect(2)
                yield()
                throw TestException2()
            }
        } catch (e: Throwable) {
            finish(4)
        }
    }

    @Test
    fun testSupervisorThrows() = runTest {
        try {
            supervisorScope {
                expect(1)
                launch {
                    expect(2)
                    delay(Long.MAX_VALUE)
                }

                launch {
                    expect(3)
                    delay(Long.MAX_VALUE)
                }

                yield()
                expect(4)
                throw TestException1()
            }
        } catch (e: TestException1) {
            finish(5)
        }
    }

    @Test
    @Ignore // JS BE bug
    fun testSupervisorThrowsWithFailingChild() = runTest(unhandled = listOf({e -> e is TestException2})) {
        try {
            supervisorScope {
                expect(1)
                launch {
                    expect(2)
                    delay(Long.MAX_VALUE)
                }

                launch {
                    expect(3)
                    try {
                        delay(Long.MAX_VALUE)
                    } finally {
                        throw TestException2()
                    }
                }

                yield()
                expect(4)
                throw TestException1()
            }
        } catch (e: TestException1) {
            finish(5)
        }
    }

    @Test
    fun testAsyncCancellation() = runTest {
        val parent = SupervisorJob()
        val deferred = async(parent) {
            expect(2)
            delay(Long.MAX_VALUE)
        }
        expect(1)
        yield()
        parent.cancel(TestException1())
        try {
            deferred.await()
            expectUnreached()
        } catch (e: TestException1) {
            finish(3)
        }
    }

    @Test
    fun testSupervisorWithParentCancelNormally() {
        val parent = Job()
        val supervisor = SupervisorJob(parent)
        supervisor.cancel()
        assertTrue(supervisor.isCancelled)
        assertFalse(parent.isCancelled)
    }

    @Test
    fun testSupervisorWithParentCancelException() {
        val parent = Job()
        val supervisor = SupervisorJob(parent)
        supervisor.cancel(TestException1())
        assertTrue(supervisor.isCancelled)
        assertTrue(parent.isCancelled)
    }

    private class TestException1 : Exception()
    private class TestException2 : Exception()
}
