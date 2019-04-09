/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.operators.*
import kotlin.test.*

class FlatMapConcatTest : FlatMapBaseTest() {

    override fun <T> Flow<T>.flatMap(mapper: suspend (T) -> Flow<T>): Flow<T> = flatMapConcat(mapper = mapper)

    @Test
    fun testFlatMapConcurrency() = runTest {
        var concurrentRequests = 0
        val flow = (1..100).asFlow().flatMapConcat { value ->
            flow {
                ++concurrentRequests
                emit(value)
                delay(Long.MAX_VALUE)
            }
        }

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
}
