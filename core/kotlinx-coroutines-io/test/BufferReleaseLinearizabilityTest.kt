/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.experimental.*
import org.junit.*

@OpGroupConfigs(
        OpGroupConfig(name = "write", nonParallel = true),
        OpGroupConfig(name = "read", nonParallel = true)
)
class BufferReleaseLinearizabilityTest : TestBase() {
    private lateinit var ch: ByteChannel

    private val lr = LinTesting()

    @Reset
    fun reset() {
        ch = ByteChannel(false)
    }

    @Operation(group = "read", runOnce = true)
    fun read() = lr.run("read") {
        ch.readLong()
    }

    @Operation(group = "write", runOnce = true)
    fun write() = lr.run("write") {
        ch.writeLong(11111)
    }

    @Operation
    fun test1() = lr.run("isClosedForRead") {
        ch.isClosedForRead
    }

    @Test
    fun test() {
        val options = StressOptions()
            .iterations(100)
            .invocationsPerIteration(1000 * stressTestMultiplier)
            .addThread(1, 2)
            .addThread(1, 2)
        LinChecker.check(BufferReleaseLinearizabilityTest::class.java, options)
    }
}