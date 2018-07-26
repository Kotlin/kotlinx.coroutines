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
class WriteBlockLinearizabilityTest : TestBase() {
    private lateinit var ch: ByteChannel

    private val lr = LinTesting()

    @Reset
    fun resetChannel() {
        ch = ByteChannel(false)
        runBlocking {
            ch.writeLong(111)
        }
    }

    @Operation(group = "read")
    fun read() = lr.run("read") {
        ch.readLong()
    }

    @Operation(group = "write")
    fun write() = lr.run("write") {
        ch.write(8) {
            it.putLong(9699)
        }
    }

    @Test
    fun test() {
        val options = StressOptions()
            .iterations(100)
            .invocationsPerIteration(1000 * stressTestMultiplier)
            .addThread(1, 1)
            .addThread(1, 1)
            .verifier(LinVerifier::class.java)
        LinChecker.check(WriteBlockLinearizabilityTest::class.java, options)
    }
}
