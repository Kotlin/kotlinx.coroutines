package kotlinx.coroutines.experimental.io

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.experimental.*
import org.junit.*

@StressCTest(iterations = 200, invocationsPerIteration = 2_000, actorsPerThread = arrayOf("1:2", "1:1", "1:1"), verifier = LinVerifier::class)
@OpGroupConfigs(
        OpGroupConfig(name = "write", nonParallel = true),
        OpGroupConfig(name = "read1", nonParallel = true),
        OpGroupConfig(name = "read2", nonParallel = true)
)
class ByteChannelJoinNoAutoFlushLinearizabilityTest {
    private lateinit var from: ByteChannel
    private lateinit var to: ByteChannel

    private val lr = LinTesting()

    @Reset
    fun reset() {
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
        LinChecker.check(ByteChannelJoinNoAutoFlushLinearizabilityTest::class.java)
    }
}
