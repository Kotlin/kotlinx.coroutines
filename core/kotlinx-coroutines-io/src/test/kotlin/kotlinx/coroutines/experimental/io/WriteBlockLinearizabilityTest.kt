package kotlinx.coroutines.experimental.io

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.experimental.*
import org.junit.*

@StressCTest(iterations = 200, invocationsPerIteration = 2_000, actorsPerThread = arrayOf("1:1", "1:1"), verifier = LinVerifier::class)
@OpGroupConfigs(
        OpGroupConfig(name = "write", nonParallel = true),
        OpGroupConfig(name = "read", nonParallel = true)
)
class WriteBlockLinearizabilityTest {
    private lateinit var ch: ByteChannel

    private val lr = LinTesting()

    @Reset
    fun reset() {
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
        LinChecker.check(WriteBlockLinearizabilityTest::class.java)
    }
}
