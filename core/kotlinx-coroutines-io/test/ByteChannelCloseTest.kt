package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.ClosedReceiveChannelException
import org.junit.After
import org.junit.Test
import java.io.IOException
import kotlin.coroutines.experimental.coroutineContext

class ByteChannelCloseTest : TestBase() {

    private val from = ByteChannel(true)
    private val to = ByteChannel(true)

    @After
    fun tearDown() {
        from.close(CancellationException())
        to.close(CancellationException())
    }

    @Test
    fun testCloseWithCause() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)

            try {
                from.copyAndClose(to) // should suspend and then throw IOException
                expectUnreached()
            } catch (expected: IOException) {
                expect(4)
            }
        }

        yield()
        expect(3)

        from.close(IOException())
        yield()

        expect(5)

        try {
            to.readInt()
            expectUnreached()
        } catch (expected: IOException) {
            finish(6)
        }
    }

    @Test
    fun testCancelWithCause() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)

            try {
                from.copyAndClose(to) // should suspend and then throw IOException
                expectUnreached()
            } catch (expected: IOException) {
                expect(4)
            }
        }

        yield()
        expect(3)

        from.cancel(IOException())
        yield()

        expect(5)

        try {
            to.readInt()
            expectUnreached()
        } catch (expected: IOException) {
            finish(6)
        }
    }

    @Test
    fun testCloseWithoutCause() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)
            from.copyAndClose(to)
            expect(4)
        }

        yield()
        expect(3)

        from.close()
        yield()

        expect(5)
        require(to.isClosedForWrite)

        try {
            to.readInt()
            expectUnreached()
        } catch (expected: ClosedReceiveChannelException) {
            finish(6)
        }
    }

    @Test
    fun testCancelWithoutCause() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)
            try {
                from.copyAndClose(to)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(4)
            }
        }

        yield()
        expect(3)

        from.cancel()
        yield()

        expect(5)
        require(to.isClosedForWrite)

        try {
            to.readInt()
            expectUnreached()
        } catch (expected: CancellationException) {
            finish(6)
        }
    }
}
