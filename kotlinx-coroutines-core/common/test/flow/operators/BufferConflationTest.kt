/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

/**
 * A _behavioral_ test for conflation options that can be configured by the [buffer] operator to test that it is
 * implemented properly and that adjacent [buffer] calls are fused properly.
*/
class BufferConflationTest : TestBase() {
    private val n = 100 // number of elements to emit for test

    private fun checkConflate(
        capacity: Int,
        onBufferOverflow: BufferOverflow = BufferOverflow.DROP_OLDEST,
        op: suspend Flow<Int>.() -> Flow<Int>
    ) = runTest {
        expect(1)
        // emit all and conflate, then collect first & last
        val expectedList = when (onBufferOverflow) {
            BufferOverflow.DROP_OLDEST -> listOf(0) + (n - capacity until n).toList() // first item & capacity last ones
            BufferOverflow.DROP_LATEST -> (0..capacity).toList() // first & capacity following ones
            else -> error("cannot happen")
        }
        flow {
            repeat(n) { i ->
                expect(i + 2)
                emit(i)
            }
        }
            .op()
            .collect { i ->
                val j = expectedList.indexOf(i)
                expect(n + 2 + j)
            }
        finish(n + 2 + expectedList.size)
    }

    @Test
    fun testConflate() =
        checkConflate(1) {
            conflate()
        }

    @Test
    fun testBufferConflated() =
        checkConflate(1) {
            buffer(Channel.CONFLATED)
        }

    @Test
    fun testBufferDropOldest() =
        checkConflate(1) {
            buffer(onBufferOverflow = BufferOverflow.DROP_OLDEST)
        }

    @Test
    fun testBuffer0DropOldest() =
        checkConflate(1) {
            buffer(0, onBufferOverflow = BufferOverflow.DROP_OLDEST)
        }

    @Test
    fun testBuffer1DropOldest() =
        checkConflate(1) {
            buffer(1, onBufferOverflow = BufferOverflow.DROP_OLDEST)
        }

    @Test
    fun testBuffer10DropOldest() =
        checkConflate(10) {
            buffer(10, onBufferOverflow = BufferOverflow.DROP_OLDEST)
        }

    @Test
    fun testConflateOverridesBuffer() =
        checkConflate(1) {
            buffer(42).conflate()
        }

    @Test // conflate().conflate() should work like a single conflate
    fun testDoubleConflate() =
        checkConflate(1) {
            conflate().conflate()
        }

    @Test
    fun testConflateBuffer10Combine() =
        checkConflate(10) {
            conflate().buffer(10)
        }

    @Test
    fun testBufferDropLatest() =
        checkConflate(1, BufferOverflow.DROP_LATEST) {
            buffer(onBufferOverflow = BufferOverflow.DROP_LATEST)
        }

    @Test
    fun testBuffer0DropLatest() =
        checkConflate(1, BufferOverflow.DROP_LATEST) {
            buffer(0, onBufferOverflow = BufferOverflow.DROP_LATEST)
        }

    @Test
    fun testBuffer1DropLatest() =
        checkConflate(1, BufferOverflow.DROP_LATEST) {
            buffer(1, onBufferOverflow = BufferOverflow.DROP_LATEST)
        }

    @Test // overrides previous buffer
    fun testBufferDropLatestOverrideBuffer() =
        checkConflate(1, BufferOverflow.DROP_LATEST) {
            buffer(42).buffer(onBufferOverflow = BufferOverflow.DROP_LATEST)
        }

    @Test // overrides previous conflate
    fun testBufferDropLatestOverrideConflate() =
        checkConflate(1, BufferOverflow.DROP_LATEST) {
            conflate().buffer(onBufferOverflow = BufferOverflow.DROP_LATEST)
        }

    @Test
    fun testBufferDropLatestBuffer7Combine() =
        checkConflate(7, BufferOverflow.DROP_LATEST) {
            buffer(onBufferOverflow = BufferOverflow.DROP_LATEST).buffer(7)
        }

    @Test
    fun testConflateOverrideBufferDropLatest() =
        checkConflate(1) {
            buffer(onBufferOverflow = BufferOverflow.DROP_LATEST).conflate()
        }

    @Test
    fun testBuffer3DropOldestOverrideBuffer8DropLatest() =
        checkConflate(3, BufferOverflow.DROP_OLDEST) {
            buffer(8, onBufferOverflow = BufferOverflow.DROP_LATEST)
            .buffer(3, BufferOverflow.DROP_OLDEST)
        }
}