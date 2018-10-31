/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.channels

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.*
import org.junit.*
import java.io.*

@Param(name = "value", gen = IntGen::class, conf = "1:3")
class ChannelLinearizabilityTest : TestBase() {

    private val lt = LinTesting()
    private var capacity = 0
    private lateinit var channel: Channel<Int>

    @Reset
    fun resetChannel() {
        channel = Channel(capacity)
    }

    @Operation(runOnce = true)
    fun send1(@Param(name = "value") value: Int) = lt.run("send1") { channel.send(value) }

    @Operation(runOnce = true)
    fun send2(@Param(name = "value") value: Int) = lt.run("send2") { channel.send(value) }

    @Operation(runOnce = true)
    fun send3(@Param(name = "value") value: Int) = lt.run("send3") { channel.send(value) }

    @Operation(runOnce = true)
    fun receive1() = lt.run("receive1") { channel.receive() }

    @Operation(runOnce = true)
    fun receive2() = lt.run("receive2") { channel.receive() }

    @Operation(runOnce = true)
    fun receive3() = lt.run("receive3") { channel.receive() }

    @Operation(runOnce = true)
    fun close1() = lt.run("close1") { channel.close(IOException("close1")) }

    @Operation(runOnce = true)
    fun close2() = lt.run("close2") { channel.close(IOException("close2")) }

    @Test
    fun testRendezvousChannelLinearizability() {
        runTest(0)
    }

    @Test
    fun testArrayChannelLinearizability() {
        for (i in listOf(1, 2, 16)) {
            runTest(i)
        }
    }

    @Test
    fun testConflatedChannelLinearizability() = runTest(Channel.CONFLATED)

    @Test
    fun testUnlimitedChannelLinearizability() = runTest(Channel.UNLIMITED)

    private fun runTest(capacity: Int) {
        this.capacity = capacity
        val options = StressOptions()
            .iterations(100)
            .invocationsPerIteration(1000 * stressTestMultiplier)
            .addThread(1, 3)
            .addThread(1, 3)
            .addThread(1, 3)
            .verifier(LinVerifier::class.java)
        LinChecker.check(ChannelLinearizabilityTest::class.java, options)
    }
}
