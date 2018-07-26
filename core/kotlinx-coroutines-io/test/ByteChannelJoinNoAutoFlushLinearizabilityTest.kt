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
        OpGroupConfig(name = "read1", nonParallel = true),
        OpGroupConfig(name = "read2", nonParallel = true)
)
class ByteChannelJoinNoAutoFlushLinearizabilityTest : TestBase() {
    private lateinit var from: ByteChannel
    private lateinit var to: ByteChannel

    private val lr = LinTesting()

    @Reset
    fun resetChannel() {
        from = ByteChannel(false)
        to = ByteChannel(false)
    }

    @Operation(runOnce = true, group = "read1")
    fun read() = lr.run("read") {
        to.readLong()
    }

    @Operation(runOnce = true, group = "write")
    fun write() = lr.run("write") {
        from.writeLong(0x1122334455667788L)
        from.flush()
    }

    @Operation(runOnce = true, group = "read2")
    fun joinTo() = lr.run("join") {
        from.joinTo(to, true)
    }

    @Test
    fun test() {
        val options = StressOptions()
            .iterations(100)
            .invocationsPerIteration(1000 * stressTestMultiplier)
            .addThread(1, 2)
            .addThread(1, 1)
            .addThread(1, 1)
            .verifier(LinVerifier::class.java)
        LinChecker.check(ByteChannelJoinNoAutoFlushLinearizabilityTest::class.java, options)
    }
}
