package benchmarks

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.*
import org.openjdk.jmh.annotations.*
import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*


/*
# Run complete. Total time: 00:01:52

Benchmark                                          Mode  Cnt     Score     Error  Units
ChannelCopyBenchmark.cioChannelCopy                avgt    5   828,087 ±  11,568  ns/op
ChannelCopyBenchmark.cioCopyToInLaunch             avgt    5  2016,028 ±  15,846  ns/op
ChannelCopyBenchmark.cioJoinToBeforeWrite          avgt    5  1413,410 ±  20,460  ns/op
ChannelCopyBenchmark.cioJoinToClosed               avgt    5   892,200 ± 113,468  ns/op
ChannelCopyBenchmark.cioJustWrite                  avgt    5   478,995 ± 106,499  ns/op
ChannelCopyBenchmark.cioJustWriteUnintercepted     avgt    5   175,821 ±  21,018  ns/op
ChannelCopyBenchmark.cioReadAndWrite               avgt    5   513,968 ±   5,142  ns/op
ChannelCopyBenchmark.cioReadAndWriteUnintercepted  avgt    5   250,731 ±   9,800  ns/op
ChannelCopyBenchmark.javaPipeConnectFirst          avgt    5   239,269 ±  11,470  ns/op
ChannelCopyBenchmark.justRunBlocking               avgt    5   228,704 ±   4,349  ns/op
ChannelCopyBenchmark.runBlockingAndLaunch          avgt    5   833,390 ±  14,968  ns/op
*/

@Warmup(iterations = 5)
@Measurement(iterations = 5)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class ChannelCopyBenchmark {
    private val HelloWorld = "Hello, World!".toByteArray()
    private val ABC = "ABC".repeat(100).toByteArray()
    private val buffer = ByteArray(4096)
    private val ioe = IOException()

    @Benchmark
    fun javaPipeConnectFirst() {
        val pipeIn = PipedInputStream()
        val pipeOut = PipedOutputStream()

        pipeIn.connect(pipeOut)

        pipeOut.write(ABC)
        var read = 0
        while (read < ABC.size) {
            val rc = pipeIn.read(buffer)
            if (rc == -1) break
            read += rc
        }

        pipeOut.close()
        pipeIn.close()
    }

    @Benchmark
    fun cioChannelCopy() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        pOut.writeFully(ABC)
        pOut.close()

        pOut.copyAndClose(pIn)

        var read = 0
        while (read < ABC.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }

    @Benchmark
    fun cioChannelCopyHW() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        pOut.writeFully(HelloWorld)
        pOut.close()

        pOut.copyAndClose(pIn)

        var read = 0
        while (read < HelloWorld.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }

    @Benchmark
    fun cioJoinToClosed() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        pOut.writeFully(ABC)
        pOut.close()

        pOut.joinTo(pIn, true)

        var read = 0
        while (read < ABC.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }

    @Benchmark
    fun cioJoinToClosedHW() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        pOut.writeFully(HelloWorld)
        pOut.close()

        pOut.joinTo(pIn, true)

        var read = 0
        while (read < HelloWorld.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }


    @Benchmark
    fun cioCopyFromEmpty() = runCoroutineFast {
        val from = ByteChannel(true)
        val to = ByteChannel(true)

        from.close()
        from.copyAndClose(to)
    }

    @Benchmark
    fun cioJoinFromEmpty() = runCoroutineFast {
        val from = ByteChannel(true)
        val to = ByteChannel(true)

        from.close()
        from.joinTo(to, true)
    }

    @Benchmark
    fun cioJoinFromEmptyNonClosed() = runCoroutineFast(allowSuspend = true) {
        val from = ByteChannel(true)
        val to = ByteChannel(true)

        from.joinTo(to, true) // should setup joining and suspend
    }

    @Benchmark
    fun cioJoinToBeforeWrite() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        launch(coroutineContext) {
            pOut.joinTo(pIn, true)
        }

        yield()

        pOut.writeFully(ABC)
        pOut.close()

        var read = 0
        while (read < ABC.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }

    @Benchmark
    fun cioJoinToHWBeforeWrite() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        launch(coroutineContext) {
            pOut.joinTo(pIn, true)
        }

        yield()

        pOut.writeFully(HelloWorld)
        pOut.close()

        var read = 0
        while (read < HelloWorld.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }

    @Benchmark
    fun cioCopyToInLaunch() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        launch(coroutineContext) {
            pOut.copyTo(pIn)
            pIn.close()
        }

        yield()

        pOut.writeFully(ABC)
        pOut.close()

        var read = 0
        while (read < ABC.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }

    @Benchmark
    fun cioCopyToHWInLaunch() = runBlocking {
        val pIn = ByteChannel(true)
        val pOut = ByteChannel(true)

        launch(coroutineContext) {
            pOut.copyTo(pIn)
            pIn.close()
        }

        yield()

        pOut.writeFully(HelloWorld)
        pOut.close()

        var read = 0
        while (read < HelloWorld.size) {
            val rc = pIn.readAvailable(buffer)
            if (rc == -1) break
            read += rc
        }

        read
    }

    @Benchmark
    fun cioJustWrite() = runBlocking {
        val c = ByteChannel()
        c.writeFully(ABC)
        c.close(ioe)
    }

    @Benchmark
    fun cioJustWriteUnintercepted() = runCoroutineFast {
        val c = ByteChannel()
        c.writeFully(ABC)
        c.close(ioe)
    }

    @Benchmark
    fun cioReadAndWrite() = runBlocking {
        val c = ByteChannel(true)
        c.writeFully(ABC)
        c.readAvailable(buffer)
        c.close()
    }

    @Benchmark
    fun cioReadAndWriteUnintercepted() = runCoroutineFast {
        val c = ByteChannel(true)
        c.writeFully(ABC)
        c.readAvailable(buffer)
        c.close()
    }

    @Benchmark
    fun justRunBlocking() = runBlocking {
    }

    @Benchmark
    fun runBlockingAndLaunch() = runBlocking {
        launch(coroutineContext) {
            yield()
        }

        yield()
    }

    private fun runCoroutineFast(allowSuspend: Boolean = false, block: suspend () -> Unit) {
        if (block.startCoroutineUninterceptedOrReturn(EmptyContinuation) === COROUTINE_SUSPENDED) {
            if (!allowSuspend)
                throw IllegalStateException("Unexpected suspend")
        }
    }

    object EmptyContinuation : Continuation<Unit> {
        override val context: CoroutineContext
            get() = EmptyCoroutineContext

        override fun resume(value: Unit) {
        }

        override fun resumeWithException(exception: Throwable) {
        }
    }
}
