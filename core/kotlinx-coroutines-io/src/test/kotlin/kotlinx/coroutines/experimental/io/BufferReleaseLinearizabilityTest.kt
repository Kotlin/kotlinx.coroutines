package kotlinx.coroutines.experimental.io

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.experimental.*
import org.junit.*

@StressCTest(iterations = 200, invocationsPerIteration = 20_000, actorsPerThread = arrayOf("1:2", "1:2"), verifier = LinVerifier::class)
@OpGroupConfigs(
        OpGroupConfig(name = "write", nonParallel = true),
        OpGroupConfig(name = "read", nonParallel = true)
)
class BufferReleaseLinearizabilityTest {
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
        LinChecker.check(BufferReleaseLinearizabilityTest::class.java)
    }
}