/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class FlatMapMergeFastPathTest : FlatMapMergeBaseTest() {

    override fun <T> Flow<T>.flatMap(mapper: suspend (T) -> Flow<T>): Flow<T> = flatMapMerge(transform = mapper).buffer(64)

    @Test
    override fun testFlatMapConcurrency() = runTest {
        var concurrentRequests = 0
        val flow = (1..100).asFlow().flatMapMerge(concurrency = 2) { value ->
            flow {
                ++concurrentRequests
                emit(value)
                delay(Long.MAX_VALUE)
            }
        }.buffer(64)

        val consumer = launch {
            flow.collect { value ->
                expect(value)
            }
        }

        repeat(4) {
            yield()
        }

        assertEquals(2, concurrentRequests)
        consumer.cancelAndJoin()
        finish(3)
    }

    @Test
    fun testCancellationExceptionDownstream() = runTest {
        val flow = flow {
            emit(1)
            hang { expect(2) }
        }.flatMapMerge {
            flow {
                emit(it)
                expect(1)
                throw CancellationException("")
            }
        }.buffer(64)

        assertFailsWith<CancellationException>(flow)
        finish(3)
    }

    @Test
    fun testCancellationExceptionUpstream() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            yield()
            throw CancellationException("")
        }.flatMapMerge {
            flow {
                expect(3)
                emit(it)
                hang { expect(4) }
            }
        }.buffer(64)

        assertFailsWith<CancellationException>(flow)
        finish(5)
    }

    @Test
    fun testCancellation() = runTest {
        val result = flow {
            emit(1)
            emit(2)
            emit(3)
            emit(4)
            expectUnreached() // Cancelled by take
            emit(5)
        }.flatMapMerge(2) { v -> flow { emit(v) } }
            .buffer(64)
            .take(2)
            .toList()
        assertEquals(listOf(1, 2), result)
    }
}
