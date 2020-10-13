/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

/**
 * Similar to [ShareInBufferTest] and [BufferConflationTest],
 * but tests [shareIn] and its fusion with [conflate] operator.
 */
class ShareInConflationTest : TestBase() {
    private val n = 100

    private fun checkConflation(
        bufferCapacity: Int,
        onBufferOverflow: BufferOverflow = BufferOverflow.DROP_OLDEST,
        op: suspend Flow<Int>.(CoroutineScope) -> Flow<Int>
    ) = runTest {
        expect(1)
        // emit all and conflate, then should collect bufferCapacity latest ones
        val done = Job()
        flow {
            repeat(n) { i ->
                expect(i + 2)
                emit(i)
            }
            done.join() // wait until done collection
            emit(-1) // signal flow completion
        }
            .op(this)
            .takeWhile { i -> i >= 0 }
            .collect { i ->
                val first = if (onBufferOverflow == BufferOverflow.DROP_LATEST) 0 else n - bufferCapacity
                val last = first + bufferCapacity - 1
                if (i in first..last) {
                    expect(n + i - first + 2)
                    if (i == last) done.complete() // received the last one
                } else {
                    error("Unexpected $i")
                }
            }
        finish(n + bufferCapacity + 2)
    }

    @Test
    fun testConflateReplay1() =
        checkConflation(1) {
            conflate().shareIn(it, SharingStarted.Eagerly, 1)
        }

    @Test // still looks like conflating the last value for the first subscriber (will not replay to others though)
    fun testConflateReplay0() =
        checkConflation(1) {
            conflate().shareIn(it, SharingStarted.Eagerly, 0)
        }

    @Test
    fun testConflateReplay5() =
        checkConflation(5) {
            conflate().shareIn(it, SharingStarted.Eagerly, 5)
        }

    @Test
    fun testBufferDropOldestReplay1() =
        checkConflation(1) {
            buffer(onBufferOverflow = BufferOverflow.DROP_OLDEST).shareIn(it, SharingStarted.Eagerly, 1)
        }

    @Test
    fun testBufferDropOldestReplay0() =
        checkConflation(1) {
            buffer(onBufferOverflow = BufferOverflow.DROP_OLDEST).shareIn(it, SharingStarted.Eagerly, 0)
        }

    @Test
    fun testBufferDropOldestReplay10() =
        checkConflation(10) {
            buffer(onBufferOverflow = BufferOverflow.DROP_OLDEST).shareIn(it, SharingStarted.Eagerly, 10)
        }

    @Test
    fun testBuffer20DropOldestReplay0() =
        checkConflation(20) {
            buffer(20, onBufferOverflow = BufferOverflow.DROP_OLDEST).shareIn(it, SharingStarted.Eagerly, 0)
        }

    @Test
    fun testBuffer7DropOldestReplay11() =
        checkConflation(18) {
            buffer(7, onBufferOverflow = BufferOverflow.DROP_OLDEST).shareIn(it, SharingStarted.Eagerly, 11)
        }

    @Test // a preceding buffer() gets overridden by conflate()
    fun testBufferConflateOverride() =
        checkConflation(1) {
            buffer(23).conflate().shareIn(it, SharingStarted.Eagerly, 1)
        }

    @Test // a preceding buffer() gets overridden by buffer(onBufferOverflow = BufferOverflow.DROP_OLDEST)
    fun testBufferDropOldestOverride() =
        checkConflation(1) {
            buffer(23).buffer(onBufferOverflow = BufferOverflow.DROP_OLDEST).shareIn(it, SharingStarted.Eagerly, 1)
        }

    @Test
    fun testBufferDropLatestReplay0() =
        checkConflation(1, BufferOverflow.DROP_LATEST) {
            buffer(onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 0)
        }

    @Test
    fun testBufferDropLatestReplay1() =
        checkConflation(1, BufferOverflow.DROP_LATEST) {
            buffer(onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 1)
        }

    @Test
    fun testBufferDropLatestReplay10() =
        checkConflation(10, BufferOverflow.DROP_LATEST) {
            buffer(onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 10)
        }

    @Test
    fun testBuffer0DropLatestReplay0() =
        checkConflation(1, BufferOverflow.DROP_LATEST) {
            buffer(0, onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 0)
        }

    @Test
    fun testBuffer0DropLatestReplay1() =
        checkConflation(1, BufferOverflow.DROP_LATEST) {
            buffer(0, onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 1)
        }

    @Test
    fun testBuffer0DropLatestReplay10() =
        checkConflation(10, BufferOverflow.DROP_LATEST) {
            buffer(0, onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 10)
        }

    @Test
    fun testBuffer5DropLatestReplay0() =
        checkConflation(5, BufferOverflow.DROP_LATEST) {
            buffer(5, onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 0)
        }

    @Test
    fun testBuffer5DropLatestReplay10() =
        checkConflation(15, BufferOverflow.DROP_LATEST) {
            buffer(5, onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 10)
        }

    @Test // a preceding buffer() gets overridden by buffer(onBufferOverflow = BufferOverflow.DROP_LATEST)
    fun testBufferDropLatestOverride() =
        checkConflation(1, BufferOverflow.DROP_LATEST) {
            buffer(23).buffer(onBufferOverflow = BufferOverflow.DROP_LATEST).shareIn(it, SharingStarted.Eagerly, 0)
        }
}