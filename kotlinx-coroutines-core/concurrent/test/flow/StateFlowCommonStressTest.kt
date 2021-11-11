/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.random.*
import kotlin.test.*

// A simplified version of StateFlowStressTest
class StateFlowCommonStressTest : TestBase() {
    private val state = MutableStateFlow<Long>(0)

    @Test
    fun testSingleEmitterAndCollector() = runMtTest {
        var collected = 0L
        val collector = launch(Dispatchers.Default) {
            // collect, but abort and collect again after every 1000 values to stress allocation/deallocation
            do {
                val batchSize = Random.nextInt(1..1000)
                var index = 0
                val cnt = state.onEach { value ->
                    // the first value in batch is allowed to repeat, but cannot go back
                    val ok = if (index++ == 0) value >= collected else value > collected
                    check(ok) {
                        "Values must be monotonic, but $value is not, was $collected"
                    }
                    collected = value
                }.take(batchSize).map { 1 }.sum()
            } while (cnt == batchSize)
        }

        var current = 1L
        val emitter = launch {
            while (true) {
                state.value = current++
                if (current % 1000 == 0L) yield() // make it cancellable
            }
        }

        delay(3000)
        emitter.cancelAndJoin()
        collector.cancelAndJoin()
        assertTrue { current >= collected / 2 }
    }
}
