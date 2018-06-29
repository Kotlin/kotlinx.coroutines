/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.internal.*
import org.junit.*
import org.junit.Test
import java.io.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class CopyAndCloseTest : TestBase() {
    private val from = ByteChannel(true)
    private val to = ByteChannel(true)

    @After
    fun tearDown() {
        from.close(CancellationException())
        to.close(CancellationException())
    }

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
    fun copyLimitedTest() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)
            val copied = from.copyTo(to, 3) // should suspend

            expect(5)

            assertEquals(3, copied)
        }

        yield()

        expect(3)
        from.writeByte(1)
        yield()

        expect(4)
        from.writeInt(2)
        yield()

        finish(6)
    }

    @Test
    fun readRemaining() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)
            from.writeFully("123".toByteArray())

            yield()
            expect(3)
            from.writeFully("456".toByteArray().asByteBuffer())

            yield()
            expect(4)
            from.close()
        }

        yield()
        assertEquals("123456", from.readRemaining().readText().toString())

        yield()

        finish(5)
    }

    @Test
    fun readRemainingLimitFailed() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)
            from.writeFully("123".toByteArray())

            yield()
            expect(3)
            from.writeFully("456".toByteArray().asByteBuffer())
        }

        yield()
        assertEquals("12345", from.readRemaining(5).readText().toString())

        finish(4)
    }


}