/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.math.*
import kotlin.test.*

/**
 * Similar to [BufferTest], but tests [shareIn] buffering and its fusion with [buffer] operators.
 */
class ShareInBufferTest : TestBase() {
    private val n = 200 // number of elements to emit for test
    private val defaultBufferSize = 64 // expected default buffer size (per docs)

    // Use capacity == -1 to check case of "no buffer"
    private fun checkBuffer(capacity: Int, op: suspend Flow<Int>.(CoroutineScope) -> Flow<Int>) = runTest {
        expect(1)
        /*
           Shared flows do not perform full rendezvous. On buffer overflow emitter always suspends until all
           subscribers get the value and then resumes. Thus, perceived batch size is +1 from buffer capacity.
         */
        val batchSize = capacity + 1
        val upstream = flow {
            repeat(n) { i ->
                val batchNo = i / batchSize
                val batchIdx = i % batchSize
                expect(batchNo * batchSize * 2 + batchIdx + 2)
                emit(i)
            }
            emit(-1) // done
        }
        coroutineScope {
            upstream
                .op(this)
                .takeWhile { i -> i >= 0 } // until done
                .collect { i ->
                    val batchNo = i / batchSize
                    val batchIdx = i % batchSize
                    // last batch might have smaller size
                    val k = min((batchNo + 1) * batchSize, n) - batchNo * batchSize
                    expect(batchNo * batchSize * 2 + k + batchIdx + 2)
                }
            coroutineContext.cancelChildren() // cancels sharing
        }
        finish(2 * n + 2)
    }

    @Test
    fun testReplay0DefaultBuffer() =
        checkBuffer(defaultBufferSize) {
            shareIn(it, SharingStarted.Eagerly)
        }

    @Test
    fun testReplay1DefaultBuffer() =
        checkBuffer(defaultBufferSize) {
            shareIn(it, SharingStarted.Eagerly, 1)
        }

    @Test // buffer is padded to default size as needed
    fun testReplay10DefaultBuffer() =
        checkBuffer(maxOf(10, defaultBufferSize)) {
            shareIn(it, SharingStarted.Eagerly, 10)
        }

    @Test // buffer is padded to default size as needed
    fun testReplay100DefaultBuffer() =
        checkBuffer( maxOf(100, defaultBufferSize)) {
            shareIn(it, SharingStarted.Eagerly, 100)
        }

    @Test
    fun testDefaultBufferKeepsDefault() =
        checkBuffer(defaultBufferSize) {
            buffer().shareIn(it, SharingStarted.Eagerly)
        }

    @Test
    fun testOverrideDefaultBuffer0() =
        checkBuffer(0) {
            buffer(0).shareIn(it, SharingStarted.Eagerly)
        }

    @Test
    fun testOverrideDefaultBuffer10() =
        checkBuffer(10) {
            buffer(10).shareIn(it, SharingStarted.Eagerly)
        }
                                         
    @Test // buffer and replay sizes add up
    fun testBufferReplaySum() =
        checkBuffer(41) {
            buffer(10).buffer(20).shareIn(it, SharingStarted.Eagerly, 11)
        }
}