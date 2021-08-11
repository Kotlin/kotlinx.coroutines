package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.koval_europar.*
import kotlinx.coroutines.scheduling.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*
import org.jetbrains.kotlinx.lincheck.verifier.*
import org.junit.*
import kotlin.random.*
import kotlin.test.*
import kotlin.test.Test

abstract class BufferedChannelLincheckTestBase(
    private val c: Channel<Int?>,
    private val sequentialSpecification: Class<*>
) : AbstractLincheckTest() {

    @Operation(cancellableOnSuspension = true, allowExtraSuspension = true)
    suspend fun send(value: Int): Any = try {
        c.send(value)
    } catch (e: NumberedCloseException) {
        e.msg
    }

//    @Operation(cancellableOnSuspension = true, allowExtraSuspension = true)
    suspend fun sendViaSelect(value: Int): Any = try {
        when (c) {
            is BufferedChannel<Int?> -> newSelect<Unit> { c.onSendNew(value) {} }
            is RendezvousChannelEuropar<Int?> -> selectEuropar<Unit> { c.onSendEuropar(value) {}  }
            else -> c.send(value)
        }
    } catch (e: NumberedCloseException) {
        e.msg
    }

//    @Operation
    fun trySend(value: Int) = c.offer(value)

    @Operation(cancellableOnSuspension = true, blocking = true)
    suspend fun receive(): Any? = try {
        c.receive()
    } catch (e: NumberedCloseException) {
        e.msg
    }

//    @Operation(cancellableOnSuspension = true, blocking = true)
    suspend fun receiveViaSelect(): Any? = try {
        when (c) {
            is BufferedChannel<Int?> -> newSelect<Int?> { c.onReceiveNew { it } }
            is RendezvousChannelEuropar<Int?> -> selectEuropar<Int?> { c.onReceiveEuropar { it }  }
            else -> c.receive()
        }
    } catch (e: NumberedCloseException) {
        e.msg
    }

//    @Operation
    fun tryReceive() = c.poll()

//    @Operation
    fun close(token: Int) = c.close(NumberedCloseException(token))

    @StateRepresentation
    fun stateRepresentation() = c.toString()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0).actorsAfter(0).sequentialSpecification(sequentialSpecification) //.actorsPerThread(3).actorsAfter(0)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) = this.invocationsPerIteration(50_000).verboseTrace()
}

private class NumberedCloseException(number: Int): Throwable() {
    val msg = "Closed($number)"
}

class BufferedChannelRendezvousLincheckTest : BufferedChannelLincheckTestBase(
    c = BufferedChannel(Channel.RENDEZVOUS),
    sequentialSpecification = SequentialRendezvousChannel::class.java
)

//class EuroParChannelRendezvousLincheckTest : BufferedChannelLincheckTestBase(
//    c = RendezvousChannelEuropar(),
//    sequentialSpecification = SequentialRendezvousChannel::class.java
//)
//
//class EuroParChannelUnlimitedLincheckTest : BufferedChannelLincheckTestBase(
//    c = object : RendezvousChannelEuropar<Int?>() {
//        override suspend fun send(element: Int?) {
//            offerUnlimited(element)
//        }
//    },
//    sequentialSpecification = SequentialUnlimitedChannel::class.java
//)
//
//class MSQueueChannelRendezvousLincheckTest : BufferedChannelLincheckTestBase(
//    c = RendezvousChannelMSQueue(),
//    sequentialSpecification = SequentialRendezvousChannel::class.java
//)

class BufferedChannel1LincheckTest : BufferedChannelLincheckTestBase(
    c = BufferedChannel(1),
    sequentialSpecification = SequentialArray1RendezvousChannel::class.java
)

class BufferedChannel2LincheckTest : BufferedChannelLincheckTestBase(
    c = BufferedChannel(2),
    sequentialSpecification = SequentialArray2RendezvousChannel::class.java
)

class BufferedChannelUnlimitedLincheckTest : BufferedChannelLincheckTestBase(
    c = BufferedChannel(Channel.UNLIMITED),
    sequentialSpecification = SequentialUnlimitedChannel::class.java
)


class NewSelectMemoryLeakStressTest : TestBase() {
    private val nRepeat = 1_000_000 * stressTestMultiplier

    @Test
    fun testLeakRegisterSend() = runTest {
        expect(1)
        val leak = BufferedChannel<String>(Channel.RENDEZVOUS)
        val data = BufferedChannel<Int>(1)
        repeat(nRepeat) { value ->
            data.send(value)
            val bigValue = bigValue() // new instance
            newSelect {
                leak.onSendNew("LEAK") {
                    println("Capture big value into this lambda: $bigValue")
                    expectUnreached()
                }
                data.onReceiveNew { received ->
                    assertEquals(value, received)
                    expect(value + 2)
                }
            }
        }
        finish(nRepeat + 2)
    }

    @Test
    fun testLeakRegisterReceive() = runTest {
        expect(1)
        val leak = BufferedChannel<String>(Channel.RENDEZVOUS)
        val data = BufferedChannel<Int>(1)
        repeat(nRepeat) { value ->
            val bigValue = bigValue() // new instance
            newSelect<Unit> {
                leak.onReceiveNew {
                    println("Capture big value into this lambda: $bigValue")
                    expectUnreached()
                }
                data.onSendNew(value) {
                    expect(value + 2)
                }
            }
            assertEquals(value, data.receive())
        }
        finish(nRepeat + 2)
    }

    // capture big value for fast OOM in case of a bug
    private fun bigValue(): ByteArray = ByteArray(4096)
}

class NewSelectLicnheckTest : AbstractLincheckTest() {
    private val c1 = BufferedChannel<Unit>(Channel.RENDEZVOUS)
    private val c2 = BufferedChannel<Unit>(Channel.RENDEZVOUS)

    @Operation
    suspend fun select(@Param(gen = ThreadIdGen::class) threadId: Int): Unit = when (threadId) {
        1 -> {
            newSelect {
                c1.onSendNew(Unit) {}
                c2.onReceiveNew {}
            }
        }
        2 -> {
            newSelect {
                c1.onReceiveNew {}
                c2.onSendNew(Unit) {}
            }
        }
        else -> error("unexpected thread id: $threadId")
    }

    override fun extractState() = Unit

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean) =
        actorsBefore(0).actorsAfter(0).threads(2)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class NewSelectUntilLicnheckTest : AbstractLincheckTest() {
    private val c1 = BufferedChannel<Unit>(1)
    private val c2 = BufferedChannel<Unit>(1)
    private var i1 = 0
    private var i2 = 0

    @Operation(cancellableOnSuspension = false, allowExtraSuspension = true)
    suspend fun selectUntil2(@Param(gen = ThreadIdGen::class) threadId: Int): Unit = when (threadId) {
        1 -> {
            newSelectUntil({ i1 < 2 }) {
                c1.onSendNew(Unit) { i1++ }
                c2.onReceiveNew { i1++ }
            }
        }
        2 -> {
            newSelectUntil({ i2 < 2 }) {
                c1.onReceiveNew { i2++ }
                c2.onSendNew(Unit) { i2++ }
            }
        }
        else -> error("unexpected thread id: $threadId")
    }

    @StateRepresentation
    fun stateRepresentation(): String = "Channel 1: $c1; Channel 2: $c2"

    override fun extractState() = Unit

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean) =
        actorsBefore(0).actorsAfter(0)
       .threads(2).actorsPerThread(1)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class ChannelStressTest : TestBase() {
    private val pool = ExperimentalCoroutineDispatcher(THREADS, THREADS, "ChannelStressTest")
    private val nSeconds = 2//3 * stressTestMultiplier

    @org.junit.Test
    fun testStress() = repeat(5) { runTest {
        val c = BufferedChannel<Int>(16)
        var sends = 0
        repeat(THREADS / 2) {
            launch(pool) {
                repeat(Int.MAX_VALUE) {
//                    if (Random.nextInt(1001) == 0) yield()
                    c.send(it)
                    sends++
                }
            }
            launch(pool) {
                repeat(Int.MAX_VALUE) {
//                    if (Random.nextInt(1001) == 0) yield()
                    c.receive()
                }
            }
        }
        delay(1000L * nSeconds)
        coroutineContext.cancelChildren()
        println("TRANSFERS: $sends")
    } }

    @org.junit.Test
    fun testStressKotlin() = repeat(4) { runTest {
        val c2 = Channel<Int>(16)

        var sends = 0
        repeat(THREADS / 2) {
            launch(pool) {
                repeat(Int.MAX_VALUE) {
//                    if (Random.nextInt(1001) == 0) yield()
                    c2.send(it)
                    sends++
                }
            }
            launch(pool) {
                repeat(Int.MAX_VALUE) {
//                    if (Random.nextInt(1001) == 0) yield()
                    c2.receive()
                }
            }
        }
        delay(1000L * nSeconds)
        coroutineContext.cancelChildren()
        println("TRANSFERS: $sends")
    } }

    @After
    fun tearDown() {
        pool.close()
    }

    private companion object {
        const val THREADS = 2
    }
}

class NewSelectStressTest : TestBase() {
    private val pool = newFixedThreadPoolContext(2, "SelectDeadlockStressTest")
    private val nSeconds = 30//3 * stressTestMultiplier

    @After
    fun tearDown() {
        pool.close()
    }

    @org.junit.Test
    fun testStress() = runTest {
        val c1 = BufferedChannel<Long>(64)
        val c2 = BufferedChannel<Long>(64)
        val s1 = Stats()
        val s2 = Stats()
        launchSendReceive(c1, c2, s1)
        launchSendReceive(c2, c1, s2)
        for (i in 1..nSeconds) {
            delay(1000)
            println("$i: First: $s1; Second: $s2; Slots per send/receive: ${c1.sendersCounter.toDouble() / s1.sendIndex} and ${c2.sendersCounter.toDouble() / s2.sendIndex};")
        }
        coroutineContext.cancelChildren()
    }

    @org.junit.Test
    fun testStressSelectLoop() = runTest {
        val c1 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val c2 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val s1 = Stats()
        val s2 = Stats()
        launchSendReceiveSelectLoop(c1, c2, s1)
        launchSendReceiveSelectLoop(c2, c1, s2)
        for (i in 1..nSeconds) {
            delay(1000)
            println("$i: First: $s1; Second: $s2; Slots per send/receive: ${c1.sendersCounter.toDouble() / s1.sendIndex} and ${c2.sendersCounter.toDouble() / s2.sendIndex}")
        }
        coroutineContext.cancelChildren()
    }

    @org.junit.Test
    fun testStressWithDummy() = runTest {
        val c = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val dummy1 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val dummy2 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val s1 = Stats()
        val s2 = Stats()
        launchSendReceive(c, dummy1, s1)
        launchSendReceive(dummy2, c, s2)
        for (i in 1..nSeconds) {
            delay(1000)
            println("$i: First: $s1; Second: $s2; Slots per send/receive: ${c.sendersCounter.toDouble() / s1.sendIndex} and ${c.sendersCounter.toDouble() / s2.sendIndex};")
        }
        coroutineContext.cancelChildren()
    }

    @org.junit.Test
    fun testStressWithDummyLoop() = runTest {
        val c = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val dummy1 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val dummy2 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val s1 = Stats()
        val s2 = Stats()
        launchSendReceiveSelectLoop(c, dummy1, s1)
        launchSendReceiveSelectLoop(dummy2, c, s2)
        for (i in 1..nSeconds) {
            delay(1000)
            println("$i: First: $s1; Second: $s2; Slots per send/receive: ${(c.sendersCounter.toDouble() + dummy1.receiversCounter) / s1.sendIndex}")
        }
        coroutineContext.cancelChildren()
    }

    private class Stats {
        var sendIndex = 0L
        var receiveIndex = 0L

        override fun toString(): String = "send=$sendIndex, received=$receiveIndex"
    }

    private fun CoroutineScope.launchSendReceive(c1: BufferedChannel<Long>, c2: BufferedChannel<Long>, s: Stats) = launch(pool) {
        while (true) {
            if (s.sendIndex % 1000 == 0L) yield()
            newSelect<Unit> {
                c1.onSendNew(s.sendIndex) {
                    s.sendIndex++
                    doGeomDistWork()
                }
                c2.onReceiveNew { i ->
                    assertEquals(s.receiveIndex, i)
                    s.receiveIndex++
                    doGeomDistWork()
                }
            }
        }
    }

    private fun doGeomDistWork() {
//        while (Random.nextInt(10) != 0) {}
    }

    private fun CoroutineScope.launchSendReceiveSelectLoop(c1: BufferedChannel<Long>, c2: BufferedChannel<Long>, s: Stats) = launch(pool) {
        newSelectUntil({ true }) {
            c1.onSendNew(s.sendIndex) {
                s.sendIndex++
                doGeomDistWork()
            }
            c2.onReceiveNew { i ->
//                assertEquals(s.receiveIndex, i)
                s.receiveIndex++
                doGeomDistWork()
            }
        }
    }
}

class NewSelectBufferedChannelTest : TestBase() {

    @Test
    fun testSelectSendSuccess() = runTest {
        expect(1)
        val channel = BufferedChannel<String>(1)
        launch {
            expect(2)
            assertEquals("OK", channel.receive())
            finish(6)
        }
        yield() // to launched coroutine
        expect(3)
        newSelect<Unit> {
            channel.onSendNew("OK") {
                expect(4)
            }
        }
        expect(5)
    }

    @Test
    fun testSelectSendReceiveBuf() = runTest {
        expect(1)
        val channel = BufferedChannel<String>(1)
        newSelect<Unit> {
            channel.onSendNew("OK") {
                expect(2)
            }
        }
        expect(3)
        newSelect<Unit> {
            channel.onReceiveNew { v ->
                expect(4)
                assertEquals("OK", v)
            }
        }
        finish(5)
    }

    @Test
    fun testSelectSendWait() = runTest {
        expect(1)
        val channel = BufferedChannel<String>(1)
        launch {
            expect(4)
            assertEquals("BUF", channel.receive())
            expect(5)
            assertEquals("OK", channel.receive())
            expect(6)
        }
        expect(2)
        channel.send("BUF")
        expect(3)
        newSelect<Unit> {
            channel.onSendNew("OK") {
                expect(7)
            }
        }
        finish(8)
    }

    @Test
    fun testSelectReceiveSuccess() = runTest {
        expect(1)
        val channel = BufferedChannel<String>(1)
        channel.send("OK")
        expect(2)
        newSelect<Unit> {
            channel.onReceiveNew { v ->
                expect(3)
                assertEquals("OK", v)
            }
        }
        finish(4)
    }

    @Test
    fun testSelectReceiveWait() = runTest {
        expect(1)
        val channel = BufferedChannel<String>(1)
        launch {
            expect(3)
            channel.send("OK")
            expect(4)
        }
        expect(2)
        newSelect<Unit> {
            channel.onReceiveNew { v ->
                expect(5)
                assertEquals("OK", v)
            }
        }
        finish(6)
    }

    @Test
    fun testSelectReceiveDispatchNonSuspending() = runTest {
        val channel = BufferedChannel<Int>(1)
        expect(1)
        channel.send(42)
        expect(2)
        launch {
            expect(4)
            newSelect<Unit> {
                channel.onReceiveNew { v ->
                    expect(5)
                    assertEquals(42, v)
                    expect(6)
                }
            }
            expect(7) // returns from select without further dispatch
        }
        expect(3)
        yield() // to launched
        finish(8)
    }

    @Test
    fun testSelectReceiveDispatchNonSuspending2() = runTest {
        val channel = BufferedChannel<Int>(1)
        expect(1)
        channel.send(42)
        expect(2)
        launch {
            expect(4)
            newSelect<Unit> {
                channel.onReceiveNew { v ->
                    expect(5)
                    assertEquals(42, v)
                    expect(6)
                    yield() // back to main
                    expect(8)
                }
            }
            expect(9) // returns from select without further dispatch
        }
        expect(3)
        yield() // to launched
        expect(7)
        yield() // again
        finish(10)
    }
}