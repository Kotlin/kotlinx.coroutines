/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.math.*
import kotlin.test.*

class BufferTest : TestBase() {
    private val n = 50 // number of elements to emit for test
    private val defaultBufferSize = 16 // expected default buffer size (per docs)

    // Use capacity == -1 to check case of "no buffer"
    private fun checkBuffer(capacity: Int, op: suspend Flow<Int>.() -> Flow<Int>) = runTest {
        expect(1)
        val batchSize = capacity + 2
        flow {
            repeat(n) { i ->
                val batchNo = i / batchSize
                val batchIdx = i % batchSize
                expect(batchNo * batchSize * 2 + batchIdx + 2)
                emit(i)
            }
        }
            .op() // insert user-defined operator
            .collect { i ->
                val batchNo = i / batchSize
                val batchIdx = i % batchSize
                // last batch might have smaller size
                val k = min((batchNo + 1) * batchSize, n) - batchNo * batchSize
                expect(batchNo * batchSize * 2 + k + batchIdx + 2)
            }
        finish(2 * n + 2)
    }

    @Test
    // capacity == -1 to checkBuffer means "no buffer" -- emits / collects are sequentially ordered
    fun testBaseline() =
        checkBuffer(-1) { this }

    @Test
    fun testBufferDefault() =
        checkBuffer(defaultBufferSize) {
            buffer()
        }

    @Test
    fun testBufferRendezvous() =
        checkBuffer(0) {
            buffer(0)
        }

    @Test
    fun testBuffer1() =
        checkBuffer(1) {
            buffer(1)
        }

    @Test
    fun testBuffer2() =
        checkBuffer(2) {
            buffer(2)
        }

    @Test
    fun testBuffer3() =
        checkBuffer(3) {
            buffer(3)
        }

    @Test
    fun testBuffer00Fused() =
        checkBuffer(0) {
            buffer(0).buffer(0)
        }

    @Test
    fun testBuffer01Fused() =
        checkBuffer(1) {
            buffer(0).buffer(1)
        }

    @Test
    fun testBuffer11Fused() =
        checkBuffer(2) {
            buffer(1).buffer(1)
        }

    @Test
    fun testBuffer111Fused() =
        checkBuffer(3) {
            buffer(1).buffer(1).buffer(1)
        }

    @Test
    fun testBuffer123Fused() =
        checkBuffer(6) {
            buffer(1).buffer(2).buffer(3)
        }

    @Test // multiple calls to buffer() create one channel of default size
    fun testBufferDefaultTwiceFused() =
        checkBuffer(defaultBufferSize) {
            buffer().buffer()
        }

    @Test // explicit buffer takes precedence of default buffer on fuse
    fun testBufferDefaultBufferFused() =
        checkBuffer(7) {
            buffer().buffer(7)
        }

    @Test // explicit buffer takes precedence of default buffer on fuse
    fun testBufferBufferDefaultFused() =
        checkBuffer(8) {
            buffer(8).buffer()
        }

    @Test // flowOn operator does not use buffer when dispatches does not change
    fun testFlowOnNameNoBuffer() =
        checkBuffer(-1) {
            flowOn(CoroutineName("Name"))
        }

    @Test // flowOn operator uses default buffer size when dispatcher changes
    fun testFlowOnDispatcherBufferDefault() =
        checkBuffer(defaultBufferSize) {
            flowOn(wrapperDispatcher())
        }

    @Test // flowOn(...).buffer(n) sets explicit buffer size to n
    fun testFlowOnDispatcherBufferFused() =
        checkBuffer(5) {
            flowOn(wrapperDispatcher()).buffer(5)
        }
    
    @Test // buffer(n).flowOn(...) sets explicit buffer size to n
    fun testBufferFlowOnDispatcherFused() =
        checkBuffer(6) {
            buffer(6).flowOn(wrapperDispatcher())
        }

    @Test // flowOn(...).buffer(n) sets explicit buffer size to n
    fun testFlowOnNameBufferFused() =
        checkBuffer(7) {
            flowOn(CoroutineName("Name")).buffer(7)
        }

    @Test // buffer(n).flowOn(...) sets explicit buffer size to n
    fun testBufferFlowOnNameFused() =
        checkBuffer(8) {
            buffer(8).flowOn(CoroutineName("Name"))
        }

    @Test // multiple flowOn/buffer all fused together
    fun testBufferFlowOnMultipleFused() =
        checkBuffer(12) {
            flowOn(wrapperDispatcher()).buffer(3)
                .flowOn(CoroutineName("Name")).buffer(4)
                .flowOn(wrapperDispatcher()).buffer(5)
        }

    @Test
    @Ignore // todo: conflated behavior is pretty useless right now, because closing channel overwrites last value
    fun testConflate() = runTest {
        expect(1)
        // emit all and conflate / then collect first & last
        flow {
            repeat(n) { i ->
                expect(i + 2)
                emit(i)
            }
        }
            .buffer(Channel.CONFLATED)
            .collect { i ->
                when (i) {
                    0 -> expect(n + 2) // first value
                    n - 1 -> expect(n + 3) // last value
                    else -> error("Unexpected $i")
                }
            }
        finish(n + 4)
    }
}

