package kotlinx.coroutines.experimental.channels

import com.devexperts.dxlab.lincheck.LinChecker
import com.devexperts.dxlab.lincheck.annotations.Operation
import com.devexperts.dxlab.lincheck.annotations.Param
import com.devexperts.dxlab.lincheck.annotations.Reset
import com.devexperts.dxlab.lincheck.paramgen.IntGen
import com.devexperts.dxlab.lincheck.stress.StressCTest
import kotlinx.coroutines.experimental.LinTesting
import kotlinx.coroutines.experimental.LinVerifier
import org.junit.Test

@StressCTest(iterations = 100, actorsPerThread = arrayOf("1:3", "1:3", "1:3"), verifier = LinVerifier::class)
@Param(name = "value", gen = IntGen::class, conf = "1:3")
class ChannelLinearizabilityTest {
    private val lt = LinTesting()
    private lateinit var channel: Channel<Int>

    @Reset
    fun reset() {
        channel = Channel<Int>()
    }

    @Operation(runOnce = true)
    fun send1(@Param(name = "value") value: Int) = lt.run("send1") { channel.send(value) }

    @Operation(runOnce = true)
    fun send2(@Param(name = "value") value: Int) = lt.run("send2") { channel.send(value) }

    @Operation(runOnce = true)
    fun send3(@Param(name = "value") value: Int) = lt.run("send3") { channel.send(value) }

    @Operation(runOnce = true)
    fun receive1() = lt.run("receive1") { channel.receive() }

    @Operation(runOnce = true)
    fun receive2() = lt.run("receive2") { channel.receive() }

    @Operation(runOnce = true)
    fun receive3() = lt.run("receive3") { channel.receive() }

//    @Operation(runOnce = true)
//    fun close1() = lt.run("close1") { channel.close(IOException("close1")) }
//
//    @Operation(runOnce = true)
//    fun close2() = lt.run("close2") { channel.close(IOException("close2")) }

    @Test
    fun testLinearizability() {
        LinChecker.check(ChannelLinearizabilityTest::class.java)
    }
}