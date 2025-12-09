package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class CoroutineScopeTestJvm: TestBase() {
    /**
     * Test the documented behavior of [CoroutineScope.newCoroutineContext] regarding the copyable context elements.
     */
    @Test
    fun testNewCoroutineContextCopyableContextElements() {
        val ce1L = MyMutableContextElement("key1", "value1_l")
        val ce2L = MyMutableContextElement("key2", "value2_l")
        val ce2R = MyMutableContextElement("key2", "value2_r")
        val ce3R = MyMutableContextElement("key3", "value3_r")
        val nonce1L = CoroutineExceptionHandler { _, _ -> }
        val nonce2L = Dispatchers.Default
        val nonce2R = Dispatchers.IO
        val nonce3R = CoroutineName("name3_r")
        val leftContext = randomlyShuffledContext(ce1L, ce2L, nonce1L, nonce2L)
        val rightContext = randomlyShuffledContext(ce2R, ce3R, nonce2R, nonce3R)
        CoroutineScope(leftContext).newCoroutineContext(rightContext).let { ctx ->
            assertEquals("Copy of 'value1_l'", ctx[MyMutableContextElementKey("key1")]?.value)
            assertEquals("Merged 'value2_l' and 'value2_r'", ctx[MyMutableContextElementKey("key2")]?.value)
            assertEquals("Copy of 'value3_r'", ctx[MyMutableContextElementKey("key3")]?.value)
            assertSame(nonce1L, ctx[CoroutineExceptionHandler])
            assertSame(nonce2R, ctx[ContinuationInterceptor])
            assertSame(nonce3R, ctx[CoroutineName])
        }
    }

    private fun randomlyShuffledContext(
        vararg elements: CoroutineContext.Element
    ): CoroutineContext = elements.toList().shuffled().fold(EmptyCoroutineContext, CoroutineContext::plus)
}

class MyMutableContextElementKey(val key: String): CoroutineContext.Key<MyMutableContextElement> {
    override fun equals(other: Any?): Boolean =
        this === other || other is MyMutableContextElementKey && key == other.key

    override fun hashCode(): Int = key.hashCode()
}

class MyMutableContextElement(
    val keyId: String,
    var value: String
) : AbstractCoroutineContextElement(MyMutableContextElementKey(keyId)), CopyableThreadContextElement<String> {
    override fun updateThreadContext(context: CoroutineContext): String {
        return value
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: String) {
        value = oldState
    }

    override fun toString(): String {
        return "MyMutableContextElement(keyId='$keyId', value='$value')"
    }

    override fun equals(other: Any?): Boolean =
        this === other || other is MyMutableContextElement && keyId == other.keyId && value == other.value

    override fun hashCode(): Int = 31 * key.hashCode() + value.hashCode()

    override fun copyForChild(): CopyableThreadContextElement<String> =
        MyMutableContextElement(keyId, "Copy of '$value'")

    override fun mergeForChild(overwritingElement: CoroutineContext.Element): CoroutineContext =
        MyMutableContextElement(
            keyId,
            "Merged '$value' and '${(overwritingElement as MyMutableContextElement).value}'"
        )
}
