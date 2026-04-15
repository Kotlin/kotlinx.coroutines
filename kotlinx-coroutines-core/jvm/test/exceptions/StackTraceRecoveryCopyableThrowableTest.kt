package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

@Suppress("UNREACHABLE_CODE", "UNUSED", "UNUSED_PARAMETER")
class StackTraceRecoveryCopyableThrowableTest : TestBase() {

    internal class Copyable(val customData: Int) : Throwable(), CopyableThrowable<Copyable> {
        // Bait
        constructor(cause: Throwable) : this(42)

        override fun createCopy(): Copyable {
            val copy = Copyable(customData)
            copy.initCause(this)
            return copy
        }
    }

    @Test
    fun testStackTraceRecovered() = runTest {
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw Copyable(239)
            }
            expectUnreached()
        } catch (e: Copyable) {
            assertEquals(239, e.customData)
            val cause = e.cause
            assertIs<Copyable>(cause)
            assertEquals(239, cause.customData)
        }
    }

    class CopyableWithCustomMessage(
        message: String?,
        cause: Throwable? = null
    ) : RuntimeException(message, cause),
        CopyableThrowable<CopyableWithCustomMessage> {

        override fun createCopy(): CopyableWithCustomMessage {
            return CopyableWithCustomMessage("Recovered: [$message]", cause)
        }
    }

    @Test
    fun testCustomCopyableMessage() = runTest {
        val result = runCatching {
            coroutineScope<Unit> {
                throw CopyableWithCustomMessage("OK")
            }
        }
        val ex = result.exceptionOrNull() ?: error("Expected to fail")
        assertIs<CopyableWithCustomMessage>(ex)
        assertEquals("Recovered: [OK]", ex.message)
    }

    @Test
    fun testTryCopyThrows() = runTest {
        class FailingException : Exception(), CopyableThrowable<FailingException> {
            override fun createCopy(): FailingException? {
                TODO("Not yet implemented")
            }
        }

        val e = FailingException()
        val result = runCatching {
            coroutineScope<Unit> {
                throw e
            }
        }

        assertSame(e, result.exceptionOrNull())
    }
}
