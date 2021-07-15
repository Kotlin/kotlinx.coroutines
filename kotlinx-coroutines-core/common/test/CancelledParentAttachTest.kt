/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlin.test.*

class CancelledParentAttachTest : TestBase() {

    @Test
    fun testAsync() = runTest {
        CoroutineStart.values().forEach { testAsyncCancelledParent(it) }
    }

    private suspend fun testAsyncCancelledParent(start: CoroutineStart) {
        try {
            withContext(Job()) {
                cancel()
                expect(1)
                val d = async<Int>(start = start) { 42 }
                expect(2)
                d.invokeOnCompletion {
                    finish(3)
                    reset()
                }
            }
            expectUnreached()
        } catch (e: CancellationException) {
            // Expected
        }
    }

    @Test
    fun testLaunch() = runTest {
        CoroutineStart.values().forEach { testLaunchCancelledParent(it) }
    }

    private suspend fun testLaunchCancelledParent(start: CoroutineStart) {
        try {
            withContext(Job()) {
                cancel()
                expect(1)
                val d = launch(start = start) { }
                expect(2)
                d.invokeOnCompletion {
                    finish(3)
                    reset()
                }
            }
            expectUnreached()
        } catch (e: CancellationException) {
            // Expected
        }
    }

    @Test
    fun testProduce() = runTest({ it is CancellationException }) {
        cancel()
        expect(1)
        val d = produce<Int> { }
        expect(2)
        (d as Job).invokeOnCompletion {
            finish(3)
            reset()
        }
    }

    @Test
    fun testBroadcast() = runTest {
        CoroutineStart.values().forEach { testBroadcastCancelledParent(it) }
    }

    private suspend fun testBroadcastCancelledParent(start: CoroutineStart) {
        try {
            withContext(Job()) {
                cancel()
                expect(1)
                val bc = broadcast<Int>(start = start) {}
                expect(2)
                (bc as Job).invokeOnCompletion {
                    finish(3)
                    reset()
                }
            }
            expectUnreached()
        } catch (e: CancellationException) {
            // Expected
        }
    }

    @Test
    fun testScopes() = runTest {
        testScope { coroutineScope { } }
        testScope { supervisorScope { } }
        testScope { flowScope { } }
        testScope { withTimeout(Long.MAX_VALUE) { } }
        testScope { withContext(Job()) { } }
        testScope { withContext(CoroutineName("")) { } }
    }

    private suspend inline fun testScope(crossinline block: suspend () -> Unit) {
        try {
            withContext(Job()) {
                cancel()
                block()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            // Expected
        }
    }
}
