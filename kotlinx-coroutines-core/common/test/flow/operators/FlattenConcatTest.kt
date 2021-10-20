/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class FlattenConcatTest : FlatMapBaseTest() {

    override fun <T> Flow<T>.flatMap(mapper: suspend (T) -> Flow<T>): Flow<T> = map(mapper).flattenConcat()

    @Test
    fun testFlatMapConcurrency() = runTest {
        var concurrentRequests = 0
        val flow = (1..100).asFlow().map { value ->
            flow {
                ++concurrentRequests
                emit(value)
                delay(Long.MAX_VALUE)
            }
        }.flattenConcat()

        val consumer = launch {
            flow.collect { value ->
                expect(value)
            }
        }

        repeat(4) {
            yield()
        }

        assertEquals(1, concurrentRequests)
        consumer.cancelAndJoin()
        finish(2)
    }

    @Test
    fun testCancellation() = runTest {
        val flow = flow {
            repeat(5) {
                emit(flow {
                    if (it == 2) throw CancellationException("")
                    emit(1)
                })
            }
        }
        assertFailsWith<CancellationException>(flow.flattenConcat())
    }
}
