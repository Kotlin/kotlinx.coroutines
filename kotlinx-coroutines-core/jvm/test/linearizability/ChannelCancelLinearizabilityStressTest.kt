/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.linearizability

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.strategy.stress.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*

@Param(name = "value", gen = IntGen::class, conf = "1:3")
class ChannelCancelLinearizabilityStressTest : TestBase() {

    private companion object {
        // Emulating ctor argument for lincheck
        var capacity = 0
    }

    private val lt = LinTesting()
    private var channel: Channel<Int> = Channel(capacity)

    @Operation(runOnce = true)
    fun send(@Param(name = "value") value: Int) = lt.run("send") { channel.send(value) }

    @Operation(runOnce = true)
    fun receive() = lt.run("receive") { channel.receive() }

    @Operation(runOnce = true)
    fun send2(@Param(name = "value") value: Int) = lt.run("send2") { channel.send(value) }

    @Operation(runOnce = true)
    fun receive2() = lt.run("receive2") { channel.receive() }

    @Operation(runOnce = true)
    fun cancel() = lt.run("cancel") { channel.cancel() }

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
        ChannelCancelLinearizabilityStressTest.capacity = capacity
        val options = StressOptions()
            .iterations(50 * stressTestMultiplierSqrt)
            .invocationsPerIteration(500 * stressTestMultiplierSqrt)
            .threads(3)
            .verifier(LinVerifier::class.java)
        LinChecker.check(ChannelCancelLinearizabilityStressTest::class.java, options)
    }
}
