package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import kotlin.test.*

@Suppress("UNREACHABLE_CODE", "UNUSED", "UNUSED_PARAMETER")
class StackTraceRecoveryCustomExceptionsTest : TestBase() {

    internal class NonCopyable(val customData: Int) : Throwable() {
        // Bait
        public constructor(cause: Throwable) : this(42)
    }

    internal class Copyable(val customData: Int) : Throwable(), CopyableThrowable<Copyable> {
        // Bait
        public constructor(cause: Throwable) : this(42)

        override fun createCopy(): Copyable {
            val copy = Copyable(customData)
            copy.initCause(this)
            return copy
        }
    }

    @Test
    fun testStackTraceNotRecovered() = runTest {
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw NonCopyable(239)
            }
            expectUnreached()
        } catch (e: NonCopyable) {
            assertEquals(239, e.customData)
            assertNull(e.cause)
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

    internal class WithDefault(message: String = "default") : Exception(message)

    @Test
    fun testStackTraceRecoveredWithCustomMessage() = runTest {
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                throw WithDefault("custom")
            }
            expectUnreached()
        } catch (e: WithDefault) {
            assertEquals("custom", e.message)
            val cause = e.cause
            assertIs<WithDefault>(cause)
            assertEquals("custom", cause.message)
        }
    }

    class WrongMessageException(token: String) : RuntimeException("Token $token")

    @Test
    fun testWrongMessageException() = runTest {
        val result = runCatching {
            coroutineScope<Unit> {
                throw WrongMessageException("OK")
            }
        }
        val ex = result.exceptionOrNull() ?: error("Expected to fail")
        assertIs<WrongMessageException>(ex)
        assertEquals("Token OK", ex.message)
    }

    @Test
    fun testNestedExceptionWithCause() = runTest {
        val result = runCatching {
            coroutineScope<Unit> {
                throw NestedException(IllegalStateException("ERROR"))
            }
        }
        val ex = result.exceptionOrNull() ?: error("Expected to fail")
        assertIs<NestedException>(ex)
        assertIs<NestedException>(ex.cause)
        val originalCause = ex.cause?.cause
        assertIs<IllegalStateException>(originalCause)
        assertEquals("ERROR", originalCause.message)
    }

    class NestedException : RuntimeException {
        constructor(cause: Throwable) : super(cause)
        constructor() : super()
    }

    @Test
    fun testWrongMessageExceptionInChannel() = runTest {
        val result = produce<Unit>(SupervisorJob() + Dispatchers.Unconfined) {
            throw WrongMessageException("OK")
        }
        val ex = runCatching {
            @Suppress("ControlFlowWithEmptyBody")
            for (unit in result) {
                // Iterator has a special code path
            }
        }.exceptionOrNull() ?: error("Expected to fail")
        assertIs<WrongMessageException>(ex)
        assertEquals("Token OK", ex.message)
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
