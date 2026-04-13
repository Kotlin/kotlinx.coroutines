package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

// Copied from StackTraceRecoveryCustomExceptionsTest
@Suppress("UNREACHABLE_CODE", "UNUSED", "UNUSED_PARAMETER")
class StackTraceRecoveryStdlibInterfaceWithTypeBoundsTest : TestBase() {

    internal class NonCopyable(val customData: Int) : Throwable() {
        // Bait
        constructor(cause: Throwable) : this(42)
    }

    internal class Copyable(val customData: Int) : Throwable(), StackTraceRecoverableWithTypeBounds<Copyable> {
        // Bait
        constructor(cause: Throwable) : this(42)

        override fun copyForStackTraceRecovery(): Copyable {
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
        StackTraceRecoverableWithTypeBounds<CopyableWithCustomMessage> {

        override fun copyForStackTraceRecovery(): CopyableWithCustomMessage {
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
        class FailingException : Exception(), StackTraceRecoverableWithTypeBounds<FailingException> {
            override fun copyForStackTraceRecovery(): FailingException {
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

    @Test
    fun testImplementationOverriding() = runTest {
        open class FailingException(
            val data: String
        ) : Exception(), StackTraceRecoverableWithTypeBounds<FailingException> {
            override fun copyForStackTraceRecovery(): FailingException? {
                return FailingException("This will not be invoked")
            }
        }
        open class FailingExceptionChild(data: String): FailingException(data) {
            override fun copyForStackTraceRecovery(): FailingExceptionChild? {
                return FailingExceptionChild("This will be the result")
            }
        }
        class FailingExceptionGrandchild: FailingExceptionChild("Something")
        val result = runCatching {
            coroutineScope<Unit> {
                throw FailingExceptionGrandchild()
            }
        }
        val ex = result.exceptionOrNull() ?: error("Expected to fail")
        assertIs<FailingExceptionChild>(ex)
        assertEquals("This will be the result", ex.data)
    }
}

private interface StackTraceRecoverableWithTypeBounds<E>
    where E : Throwable, E : StackTraceRecoverableWithTypeBounds<E>
{
    fun copyForStackTraceRecovery(): E?
}
