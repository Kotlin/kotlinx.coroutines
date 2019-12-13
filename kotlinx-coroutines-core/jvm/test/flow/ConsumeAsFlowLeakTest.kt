/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import kotlin.test.*

class ConsumeAsFlowLeakTest : TestBase() {

    private data class Box(val i: Int)

    // In companion to avoid references through runTest
    companion object {
        private val first = Box(4)
        private val second = Box(5)
    }

    // @Test //ignored until KT-33986
    fun testReferenceIsNotRetained() = testReferenceNotRetained(true)

    @Test
    fun testReferenceIsNotRetainedNoSuspension() = testReferenceNotRetained(false)

    private fun testReferenceNotRetained(shouldSuspendOnSend: Boolean) = runTest {
        val channel = BroadcastChannel<Box>(1)
        val job = launch {
            expect(2)
            channel.asFlow().collect {
                expect(it.i)
            }
        }

        expect(1)
        yield()
        expect(3)
        channel.send(first)
        if (shouldSuspendOnSend) yield()
        channel.send(second)
        yield()
        assertEquals(0, FieldWalker.walk(channel).count { it === second })
        finish(6)
        job.cancelAndJoin()
    }
}
