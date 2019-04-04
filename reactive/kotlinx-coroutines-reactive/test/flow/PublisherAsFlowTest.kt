/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import kotlin.test.*

class PublisherAsFlowTest : TestBase() {

    @Test
    fun testCancellation() = runTest {
        var onNext = 0
        var onCancelled = 0
        var onError = 0

        val publisher = publish {
            coroutineContext[Job]?.invokeOnCompletion {
                if (it is CancellationException) ++onCancelled
            }

            repeat(100) {
                send(it)
            }
        }

        publisher.asFlow().launchIn(CoroutineScope(Dispatchers.Unconfined)) {
            onEach {
                ++onNext
                throw RuntimeException()
            }
            catch<Throwable> {
                ++onError
            }
        }.join()


        assertEquals(1, onNext)
        assertEquals(1, onError)
        assertEquals(1, onCancelled)
    }
}