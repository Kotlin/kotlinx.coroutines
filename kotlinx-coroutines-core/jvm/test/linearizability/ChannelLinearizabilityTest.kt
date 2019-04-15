/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.linearizability

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.strategy.stress.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import org.junit.*
import java.io.*

@Ignore
@Param(name = "value", gen = IntGen::class, conf = "0:10")
class ChannelLinearizabilityTest : TestBase() {

    private companion object {
        // Emulating ctor argument for Lin-Check
        var capacity = 0
    }

    private val lt = LinTesting()
    private var channel: Channel<Int> = Channel(capacity)

    @Operation(runOnce = true)
    fun send1(@Param(name = "value") value: Int) = lt.run("send1") { channel.send(value) }

    @Operation(runOnce = true)
    fun send2(@Param(name = "value") value: Int) = lt.run("send2") { channel.send(value) }

    @Operation(runOnce = true)
    fun sendSelect1(@Param(name = "value") value: Int) = lt.run("sendSelect1") {
        select<Unit> { channel.onSend(value) {} }
    }

    @Operation(runOnce = true)
    fun sendSelect2(@Param(name = "value") value: Int) = lt.run("sendSelect2") {
        select<Unit> { channel.onSend(value) {} }
    }

    @Operation(runOnce = true)
    fun receive1() = lt.run("receive1") { channel.receive() }

    @Operation(runOnce = true)
    fun receive2() = lt.run("receive2") { channel.receive() }

    @Operation(runOnce = true)
    fun receiveSelect1() = lt.run("receiveSelect1") {
        select<Int> { channel.onReceive { it } }
    }

    @Operation(runOnce = true)
    fun receiveSelect2() = lt.run("receiveSelect2") {
        select<Int> { channel.onReceive { it } }
    }

    @Operation(runOnce = true)
    fun close1() = lt.run("close1") { channel.close(IOException("close1")) }

//    @Operation(runOnce = true)
//    fun close2() = lt.run("close2") { channel.close(IOException("close2")) }

//    @Operation(runOnce = true)
//    fun cancel1() = lt.run("cancel1") { channel.cancel(CancellationException("cancel1")) }

    @Operation(runOnce = true)
    fun isClosedForSend1() = lt.run("isClosedForSend1") { channel.isClosedForSend }

    @Operation(runOnce = true)
    fun isClosedForReceive1() = lt.run("isClosedForReceive1") { channel.isClosedForReceive }

    @Operation(runOnce = true, handleExceptionsAsResult = [IOException::class])
    fun offer1(@Param(name = "value") value: Int) = lt.run("offer1") { channel.offer(value) }

    @Operation(runOnce = true, handleExceptionsAsResult = [IOException::class])
    fun offer2(@Param(name = "value") value: Int) = lt.run("offer2") { channel.offer(value) }

    @Operation(runOnce = true, handleExceptionsAsResult = [IOException::class])
    fun poll1() = lt.run("poll1") { channel.poll() }

    @Operation(runOnce = true, handleExceptionsAsResult = [IOException::class])
    fun poll2() = lt.run("poll2") { channel.poll() }

    @Test
    fun testRendezvousChannelLinearizability() = runTest(Channel.RENDEZVOUS)

    @Test
    fun testArrayChannelLinearizability() = listOf(1).forEach { runTest(it) }

    @Ignore
    @Test
    fun testConflatedChannelLinearizability() = runTest(Channel.CONFLATED)

    @Test
    fun testUnlimitedChannelLinearizability() = runTest(Channel.UNLIMITED)

    private fun runTest(capacity: Int) {
        ChannelLinearizabilityTest.capacity = capacity
        val options = StressOptions()
            .iterations(100 * stressTestMultiplierSqrt)
            .invocationsPerIteration(5000 * stressTestMultiplierSqrt)
            .threads(3)
            .verifier(LinVerifier::class.java)
            .logLevel(LoggingLevel.DEBUG)
        LinChecker.check(ChannelLinearizabilityTest::class.java, options)
    }
}
