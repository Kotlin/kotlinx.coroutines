/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.util.concurrent.atomic.*
import kotlin.coroutines.*
import kotlin.test.*

class ReusableCancellableContinuationStressTest : TestBase() {

    private var continuation: Continuation<Int>? = null

    @Test
    fun testMemoryLeak() = runTest {
        val iterations = 100_000 * stressTestMultiplier
        val d1 = async {
            val myState = AtomicInteger(0)
            repeat(iterations) {
                stateMachine(it, myState)
            }
        }

        val d2 = async {
            val myState = AtomicInteger(0)
            repeat(iterations) {
                stateMachine(it, myState)
            }
        }

        awaitAll(d1, d2)
    }

    private suspend fun stateMachine(counter: Int, myState: AtomicInteger) {
        if (continuation == null) {
            val value = suspendAtomicCancellableCoroutineReusable<Int> {
                continuation = it
            }

            assertEquals(counter / 2, value)
        } else {
            val cont = continuation
            continuation = null
            cont!!.resume(myState.getAndIncrement())
        }
    }
}