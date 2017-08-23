package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import org.junit.*
import java.io.*
import kotlin.test.*

class CopyAndCloseTest : TestBase() {
    private val from = ByteChannel(true)
    private val to = ByteChannel(true)

    @Test
    fun smokeTest() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)
            val copied = from.copyAndClose(to) // should suspend

            expect(7)

            assertEquals(8, copied)
        }

        yield()

        expect(3)
        from.writeInt(1)
        expect(4)
        from.writeInt(2)
        expect(5)

        yield()
        expect(6)

        from.close()
        yield()

        finish(8)
    }

    @Test
    fun failurePropagation() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)

            try {
                from.copyAndClose(to) // should suspend and then throw IOException
                fail("Should rethrow exception")
            } catch (expected: IOException) {
            }

            expect(4)
        }

        yield()
        expect(3)

        from.close(IOException())
        yield()

        expect(5)

        try {
            to.readInt()
            fail("Should throw exception")
        } catch (expected: IOException) {
        }

        finish(6)
    }
}