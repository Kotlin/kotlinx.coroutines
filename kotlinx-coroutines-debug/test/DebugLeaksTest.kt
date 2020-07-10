/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import kotlinx.coroutines.debug.internal.*
import org.junit.*

/**
 * This is fast but fragile version of [DebugLeaksStressTest] that check reachability of a captured object
 * in [DebugProbesImpl] via [FieldWalker].
 */
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
class DebugLeaksTest : DebugTestBase() {
    private class Captured

    @Test
    fun testIteratorLeak() {
        val captured = Captured()
        iterator { yield(captured) }
        assertNoCapturedReference()
    }

    @Test
    fun testLazyGlobalCoroutineLeak() {
        val captured = Captured()
        GlobalScope.launch(start = CoroutineStart.LAZY) { println(captured) }
        assertNoCapturedReference()
    }

    @Test
    fun testLazyCancelledChildCoroutineLeak() = runTest {
        val captured = Captured()
        coroutineScope {
            val child = launch(start = CoroutineStart.LAZY) { println(captured) }
            child.cancel()
        }
        assertNoCapturedReference()
    }

    @Test
    fun testAbandonedGlobalCoroutineLeak() {
        val captured = Captured()
        GlobalScope.launch {
            suspendForever()
            println(captured)
        }
        assertNoCapturedReference()
    }

    private suspend fun suspendForever() = suspendCancellableCoroutine<Unit> {  }

    private fun assertNoCapturedReference() {
        FieldWalker.assertReachableCount(0, DebugProbesImpl, rootStatics = true) { it is Captured }
    }
}