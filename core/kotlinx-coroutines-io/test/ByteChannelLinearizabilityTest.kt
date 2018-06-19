package kotlinx.coroutines.experimental.io

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.experimental.*
import org.junit.*

@Param(name = "value", gen = IntGen::class, conf = "1:8192")
@OpGroupConfigs(
        OpGroupConfig(name = "write", nonParallel = true),
        OpGroupConfig(name = "read", nonParallel = true)
)
class ByteChannelLinearizabilityTest : TestBase() {
    private lateinit var channel: ByteChannel
    private val lr = LinTesting()

    @Reset
    fun reset() {
        channel = ByteChannel()
    }

    @Operation(runOnce = true, group = "write")
    fun writeInt1(@Param(name = "value") value: Int) = lr.run("writeInt1") {
        channel.writeInt(value)
    }

    @Operation(runOnce = true, group = "write")
    fun writeInt2(@Param(name = "value") value: Int) = lr.run("writeInt2") {
        channel.writeInt(value)
    }

    @Operation(runOnce = true, group = "read")
    fun readInt1() = lr.run("readInt1") {
        channel.readInt()
    }

    @Operation(runOnce = true, group = "read")
    fun readInt2() = lr.run("readInt2") {
        channel.readInt()
    }

    @Operation(group = "write")
    fun close() = lr.run("close") {
        channel.close()
    }

    @Operation
    fun flush() = lr.run("flush") {
        channel.flush()
    }

    @Test
    fun test() {
        val options = StressOptions()
            .iterations(100)
            .invocationsPerIteration(1000 * stressTestMultiplier)
            .addThread(1, 1)
            .addThread(1, 1)
            .addThread(1, 1)
            .verifier(LinVerifier::class.java)
        LinChecker.check(ByteChannelLinearizabilityTest::class.java, options)
    }
}