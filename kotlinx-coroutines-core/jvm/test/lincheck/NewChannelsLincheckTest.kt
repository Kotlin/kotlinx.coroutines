package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.junit.*
import kotlin.test.*
import kotlin.test.Test

abstract class BufferedChannelLincheckTestBase(
    private val c: BufferedChannel<Int>,
    private val sequentialSpecification: Class<*>
) : AbstractLincheckTest() {

    @Operation(cancellableOnSuspension = true, causesBlocking = true, allowExtraSuspension = true)
    suspend fun send(value: Int) = c.send(value)

    @Operation(cancellableOnSuspension = true, causesBlocking = true, allowExtraSuspension = true)
    suspend fun sendViaSelect(value: Int) = newSelect<Unit> {
        c.onSend(value) {}
    }

//    @Operation
    fun trySend(value: Int) = c.offer(value)

    @Operation(cancellableOnSuspension = true)
    suspend fun receive() = c.receive()

    @Operation(cancellableOnSuspension = true, causesBlocking = true)
    suspend fun receiveViaSelect() = newSelect<Int> {
        c.onReceive { it }
    }

//    @Operation
    fun tryReceive() = c.poll()

    @StateRepresentation
    fun stateRepresentation() = c.toString()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0).sequentialSpecification(sequentialSpecification)
}

class BufferedChannelRendezvousLincheckTest : BufferedChannelLincheckTestBase(
    c = BufferedChannel(Channel.RENDEZVOUS),
    sequentialSpecification = SequentialRendezvousChannel::class.java
)

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
                leak.onSend("LEAK") {
                    println("Capture big value into this lambda: $bigValue")
                    expectUnreached()
                }
                data.onReceive { received ->
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
                leak.onReceive {
                    println("Capture big value into this lambda: $bigValue")
                    expectUnreached()
                }
                data.onSend(value) {
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

class NewSelectDeadlockStressTest : TestBase() {
    private val pool = newFixedThreadPoolContext(2, "SelectDeadlockStressTest")
    private val nSeconds = 3 * stressTestMultiplier

    @After
    fun tearDown() {
        pool.close()
    }

    @org.junit.Test
    fun testStress() = runTest {
        val c1 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val c2 = BufferedChannel<Long>(Channel.RENDEZVOUS)
        val s1 = Stats()
        val s2 = Stats()
        launchSendReceive(c1, c2, s1)
        launchSendReceive(c2, c1, s2)
        for (i in 1..nSeconds) {
            delay(1000)
            println("$i: First: $s1; Second: $s2")
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
                c1.onSend(s.sendIndex) {
                    s.sendIndex++
                }
                c2.onReceive { i ->
                    assertEquals(s.receiveIndex, i)
                    s.receiveIndex++
                }
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
            channel.onSend("OK") {
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
            channel.onSend("OK") {
                expect(2)
            }
        }
        expect(3)
        newSelect<Unit> {
            channel.onReceive { v ->
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
            channel.onSend("OK") {
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
            channel.onReceive { v ->
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
            channel.onReceive { v ->
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
                channel.onReceive { v ->
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
                channel.onReceive { v ->
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