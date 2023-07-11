/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */


package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

abstract class FlatMapMergeBaseTest : FlatMapBaseTest() {
    @Test
    fun testFailureCancellation() = runTest {
        val flow = flow {
            expect(2)
            emit(1)
            expect(3)
            emit(2)
            expect(4)
        }.flatMap {
            if (it == 1) flow {
                hang { expect(6) }
            } else flow<Int> {
                expect(5)
                throw TestException()
            }
        }

        expect(1)
        assertFailsWith<TestException> { flow.singleOrNull() }
        finish(7)
    }

    @Test
    fun testConcurrentFailure() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            expect(2)
            emit(1)
            expect(3)
            emit(2)
        }.flatMap {
            if (it == 1) flow<Int> {
                expect(5)
                latch.send(Unit)
                hang {
                    expect(7)
                    throw TestException2()

                }
            } else {
                expect(4)
                latch.receive()
                expect(6)
                throw TestException()
            }
        }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(8)
    }

    @Test
    fun testFailureInMapOperationCancellation() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            expect(2)
            emit(1)
            expect(3)
            emit(2)
            expectUnreached()
        }.flatMap {
            if (it == 1) flow {
                expect(5)
                latch.send(Unit)
                hang { expect(7) }
            } else {
                expect(4)
                latch.receive()
                expect(6)
                throw TestException()
            }
        }

        expect(1)
        assertFailsWith<TestException> { flow.count() }
        finish(8)
    }

    @Test
    abstract fun testFlatMapConcurrency(): TestResult
}
