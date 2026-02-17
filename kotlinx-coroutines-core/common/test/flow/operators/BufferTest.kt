package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import kotlin.math.*
import kotlin.test.*

/**
 * A _behavioral_ test for buffering that is introduced by the [buffer] operator to test that it is
 * implemented properly and that adjacent [buffer] calls are fused properly.
 */
class BufferTest : TestBase() {
    private val n = 200 // number of elements to emit for each test
    private val defaultBufferSize = 64 // expected default buffer size (per docs)

    // Use capacity == -1 to check case of "no buffer"
    private fun checkBufferDispatched(capacity: Int, op: suspend Flow<Int>.() -> Flow<Int>) = runTest {
        /*
           Channels perform full rendezvous. Sender does not suspend when there is a suspended receiver and vice versa.
           Thus, the perceived batch size is +2 from capacity when the sender coroutine is dispatched.
         */
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

    // Use capacity == -1 to check the case of "no buffer"
    internal fun checkBuffer(capacity: Int, op: suspend Flow<Int>.() -> Flow<Int>) = runTest {
        /*
           The perceived capacity is capacity + 1 for the first batch and capacity + 2 for future batches
            for the undispatched sender coroutine.

           Depending on the op, the sender coroutine can be launched as dispatched or undispatched.
           E.g., flowOn with a different dispatcher is always dispatched, while only `.buffer(...)` is undispatched.

           If the coroutine launched undispatched (the most common case in these tests,
           e.g. `flow { ... }.buffer(3).collect()`), the sender will arrive before the receiver subscribed,
           thus making the perceived capacity +1 from capacity for the first batch, and +2 from capacity on
           all the later batches.

           In addition to that, the sender also gets to execute first and populate the buffer.
           See tests named *Explicit* below to understand the execution order.
         */
        expect(1)
        val batchSize = capacity + 2
        val firstBatchSize = min(n, capacity + 1)
        flow {
            repeat(n) { i ->
                if (i < firstBatchSize) {
                    expect(i + 2)  // the first expect for i == 0 is expect(1)
                } else {
                    val batchNo = ((i - firstBatchSize) / batchSize) + 1
                    val batchIdx = (i - firstBatchSize) % batchSize
                    expect(2 * (firstBatchSize + (batchNo - 1) * batchSize) + batchIdx + 2)
                }
                emit(i)
            }
        }
            .op() // insert user-defined operator
            .collect { i ->
                if (i < firstBatchSize) {
                    expect(firstBatchSize + i + 2)
                } else {
                    val batchNo = ((i - firstBatchSize) / batchSize) + 1
                    val batchIdx = (i - firstBatchSize) % batchSize
                    // last batch might have smaller size
                    val curBatchSize =
                        min(firstBatchSize + batchNo * batchSize, n) - (firstBatchSize + (batchNo - 1) * batchSize)
                    expect(2 * (firstBatchSize + (batchNo - 1) * batchSize) + curBatchSize + batchIdx + 2)
                }
            }
        finish(2 * n + 2)
    }

    @Test
    // capacity == -1 to checkBuffer means "no buffer" -- emits / collects are sequentially ordered
    fun testBaseline() =
        checkBuffer(-1) { this }

    @Test
    fun testBufferRendezvousExplicitSimple() = runTest {
        flow {
            expect(1)
            emit("a")  // suspends to wait for a receiver
            expect(3)
        }
            .buffer(0)
            .collect { value ->
                assertEquals("a", value)
                expect(2)
            }
        finish(4)
    }

    @Test
    fun testBufferRendezvousExplicit() = runTest {
        flow {
            expect(1)
            emit("a")  // suspends waiting for the receiver
            expect(3)
            emit("b")  // doesn't suspend, because the receiver is already waiting
            expect(4)
            emit("c")  // suspends waiting for the receiver
            expect(7)
        }
            .buffer(0)
            .collect {
                when (it) {
                    "a" -> expect(2)
                    "b" -> expect(5)
                    "c" -> expect(6)
                }
            }
        finish(8)
    }

    @Test
    fun testBuffer2Explicit() = runTest {
        flow {
            expect(1)
            emit("a")  // doesn't suspend, buffer has space
            expect(2)
            emit("b")  // doesn't suspend, buffer has space
            expect(3)
            emit("c")  // suspends until the buffer has space
            expect(7)
            emit("d")  // doesn't suspend, the receiver is waiting
            expect(8)
            emit("e")  // doesn't suspend, buffer has space
            expect(9)
            emit("f")  // doesn't suspend, buffer has space
            expect(10)
            emit("g")  // suspends until the buffer has space
            expect(15)
            emit("h")  // doesn't suspend, the receiver is waiting
            expect(16)
        }
            .buffer(2)
            .collect {
                when (it) {
                    "a" -> expect(4)
                    "b" -> expect(5)
                    "c" -> expect(6)
                    "d" -> expect(11)
                    "e" -> expect(12)
                    "f" -> expect(13)
                    "g" -> expect(14)
                    "h" -> expect(17)
                    else -> expectUnreached()
                }
            }
        finish(18)
    }

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
    fun testBufferNotCompletelyFilled() =
        checkBuffer(n + 10) {
            buffer(n + 10)
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
        checkBufferDispatched(defaultBufferSize) {
            flowOn(wrapperDispatcher())
        }

    @Test // flowOn(...).buffer(n) sets explicit buffer size to n
    fun testFlowOnDispatcherBufferFused() =
        checkBufferDispatched(5) {
            flowOn(wrapperDispatcher()).buffer(5)
        }

    @Test // buffer(n).flowOn(...) sets explicit buffer size to n
    fun testBufferFlowOnDispatcherFused() =
        checkBufferDispatched(6) {
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
        checkBufferDispatched(12) {
            flowOn(wrapperDispatcher()).buffer(3)
                .flowOn(CoroutineName("Name")).buffer(4)
                .flowOn(wrapperDispatcher()).buffer(5)
        }

    @Test
    fun testCancellation() = runTest {
        val result = flow {
            emit(1)
            emit(2)
            emit(3)
            expectUnreached()
            emit(4)
        }.buffer(0)
            .take(2)
            .toList()
        assertEquals(listOf(1, 2), result)
    }

    @Test
    fun testFailsOnIllegalArguments() {
        val flow = emptyFlow<Int>()
        assertFailsWith<IllegalArgumentException> { flow.buffer(capacity = -3) }
        assertFailsWith<IllegalArgumentException> { flow.buffer(capacity = Int.MIN_VALUE) }
        assertFailsWith<IllegalArgumentException> {
            flow.buffer(
                capacity = Channel.CONFLATED,
                onBufferOverflow = BufferOverflow.DROP_LATEST
            )
        }
        assertFailsWith<IllegalArgumentException> {
            flow.buffer(
                capacity = Channel.CONFLATED,
                onBufferOverflow = BufferOverflow.DROP_OLDEST
            )
        }
    }
}

