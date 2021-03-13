/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import org.junit.Test
import kotlin.test.*

class ReusableCancellableContinuationLeakStressTest : TestBase() {

    @Suppress("UnnecessaryVariable")
    private suspend fun <T : Any> ReceiveChannel<T>.receiveBatch(): T {
        val r = receive() // DO NOT MERGE LINES, otherwise TCE will kick in
        return r
    }

    private val iterations = 100_000 * stressTestMultiplier

    class Leak(val i: Int)

    @Test // Simplified version of #2564
    fun testReusableContinuationLeak() = runTest {
        val channel = produce(capacity = 1) { // from the main thread
            (0 until iterations).forEach {
                send(Leak(it))
            }
        }

        launch(Dispatchers.Default) {
            repeat (iterations) {
                val value = channel.receiveBatch()
                assertEquals(it, value.i)
            }
            (channel as Job).join()

            FieldWalker.assertReachableCount(0, coroutineContext.job, false) { it is Leak }
        }
    }
}
