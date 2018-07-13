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
class ChannelIsClosedLinearizabilityTest : TestBase() {

    private val lt = LinTesting()
    private lateinit var channel: Channel<Int>

    @Reset
    fun resetChannel() {
        channel = Channel()
    }

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
            .iterations(100)
            .invocationsPerIteration(1000 * stressTestMultiplier)
            .addThread(1, 3)
            .addThread(1, 3)
            .addThread(1, 3)
            .verifier(LinVerifier::class.java)
            .injectExecution { actors, methods ->
                actors[0].add(actorMethod(methods, "receive1"))
                actors[0].add(actorMethod(methods, "receive2"))
                actors[0].add(actorMethod(methods, "close1"))

                actors[1].add(actorMethod(methods, "send2"))
                actors[1].add(actorMethod(methods, "send1"))

                actors[2].add(actorMethod(methods, "isClosedForSend"))
            }

        LinChecker.check(ChannelIsClosedLinearizabilityTest::class.java, options)
    }
}
