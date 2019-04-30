/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

// See https://github.com/Kotlin/kotlinx.coroutines/issues/1128
class IdFlowTest : TestBase() {
    @Test
    fun testCancelInCollect() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        flow {
            expect(2)
            emit(1)
            expect(3)
            hang { finish(6) }
        }.idScoped().collect { value ->
            expect(4)
            assertEquals(1, value)
            kotlin.coroutines.coroutineContext.cancel()
            expect(5)
        }
        expectUnreached()
    }

    @Test
    fun testCancelInFlow() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        flow {
            expect(2)
            emit(1)
            kotlin.coroutines.coroutineContext.cancel()
            expect(3)
        }.idScoped().collect { value ->
            finish(4)
            assertEquals(1, value)
        }
        expectUnreached()
    }
}

/**
 * This flow should be "identity" function with respect to cancellation.
 */
private fun <T> Flow<T>.idScoped(): Flow<T> = flow {
    coroutineScope {
        val channel = produce {
            collect { send(it) }
        }
        channel.consumeEach {
            emit(it)
        }
    }
}
