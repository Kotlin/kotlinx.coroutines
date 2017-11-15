package benchmarks

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.*
import org.openjdk.jmh.annotations.*
import java.io.*
import java.nio.*
import java.util.concurrent.*

@Warmup(iterations = 5)
@Measurement(iterations = 5)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Benchmark)
@Fork(1)
open class ChannelCopyBenchmark {
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
    fun cioJustWrite() = runBlocking {
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
    fun justRunBlocking() = runBlocking {
    }

    @Benchmark
    fun runBlockingAndLaunch() = runBlocking {
        launch(coroutineContext) {
            yield()
        }

        yield()
    }

//    @Benchmark
    fun javaPipeConnectAfterWrite() {
        val pipeIn = PipedInputStream()
        val pipeOut = PipedOutputStream()

        pipeOut.write("ABC".toByteArray())
        pipeIn.connect(pipeOut)
        pipeIn.read(buffer)

        pipeOut.close()
        pipeIn.close()
    }
}
