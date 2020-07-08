/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import org.junit.*

/**
 * This stress tests ensure that no actual [OutOfMemoryError] occurs when lots of coroutines are created and
 * leaked in various ways under debugger. A faster but more fragile version of this test is in [DebugLeaksTest].
 */
class DebugLeaksStressTest : DebugTestBase() {
    private val nRepeat = 100_000 * stressTestMultiplier
    private val nBytes = 100_000

    @Test
    fun testIteratorLeak() {
        repeat(nRepeat) {
            val bytes = ByteArray(nBytes)
            iterator { yield(bytes) }
        }
    }

    @Test
    fun testLazyGlobalCoroutineLeak() {
        repeat(nRepeat) {
            val bytes = ByteArray(nBytes)
            GlobalScope.launch(start = CoroutineStart.LAZY) { println(bytes) }
        }
    }

    @Test
    fun testLazyCancelledChildCoroutineLeak() = runTest {
        coroutineScope {
            repeat(nRepeat) {
                val bytes = ByteArray(nBytes)
                val child = launch(start = CoroutineStart.LAZY) { println(bytes) }
                child.cancel()
            }
        }
    }

    @Test
    fun testAbandonedGlobalCoroutineLeak() {
        repeat(nRepeat) {
            val bytes = ByteArray(nBytes)
            GlobalScope.launch {
                suspendForever()
                println(bytes)
            }
        }
    }

    private suspend fun suspendForever() = suspendCancellableCoroutine<Unit> {  }
}
