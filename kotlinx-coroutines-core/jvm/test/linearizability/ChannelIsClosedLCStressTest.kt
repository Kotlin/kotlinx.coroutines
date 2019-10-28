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
import java.io.*

@Param(name = "value", gen = IntGen::class, conf = "1:3")
class ChannelIsClosedLCStressTest : TestBase() {

    private val lt = LinTesting()
    private val channel = Channel<Int>()

    @Operation(runOnce = true)
    fun send1(@Param(name = "value") value: Int) = lt.run("send1") { channel.send(value) }

    @Operation(runOnce = true)
    fun send2(@Param(name = "value") value: Int) = lt.run("send2") { channel.send(value) }

    @Operation(runOnce = true)
    fun receive1() = lt.run("receive1") { channel.receive() }

    @Operation(runOnce = true)
    fun receive2() = lt.run("receive2") { channel.receive() }

    @Operation(runOnce = true)
    fun close1() = lt.run("close1") { channel.close(IOException("close1")) }

    @Operation(runOnce = true)
    fun isClosedForReceive() = lt.run("isClosedForReceive") { channel.isClosedForReceive }

    @Operation(runOnce = true)
    fun isClosedForSend() = lt.run("isClosedForSend") { channel.isClosedForSend }

    @Test
    fun testLinearizability() {
        val options = StressOptions()
            .iterations(100 * stressTestMultiplierSqrt)
            .invocationsPerIteration(1000 * stressTestMultiplierSqrt)
            .threads(3)
            .verifier(LinVerifier::class.java)

        LinChecker.check(ChannelIsClosedLCStressTest::class.java, options)
    }
}
