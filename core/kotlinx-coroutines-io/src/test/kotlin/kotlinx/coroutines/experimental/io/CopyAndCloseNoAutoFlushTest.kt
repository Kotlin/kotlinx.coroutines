package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.io.internal.BufferObjectPool
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.yield
import org.junit.Rule
import org.junit.Test
import org.junit.rules.TestRule
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class CopyAndCloseNoAutoFlushTest : TestBase() {
    private val verifyingPool = VerifyingObjectPool(BufferObjectPool)

    private val from = ByteBufferChannel(true, verifyingPool)
    private val to = ByteBufferChannel(false, verifyingPool)

    @get:Rule
    val pool get() = verifyingPool as TestRule

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

        yield()
        assertEquals(4, to.availableForRead) // 4 bytes need to be copied in spite of that there is no autoFlush

        from.writeInt(2)
        expect(5)

        yield()
        expect(6)

        from.close()
        yield()

        assertTrue { to.isClosedForWrite }
        to.readPacket(8).release()
        assertTrue { to.isClosedForRead }

        finish(8)
    }
}