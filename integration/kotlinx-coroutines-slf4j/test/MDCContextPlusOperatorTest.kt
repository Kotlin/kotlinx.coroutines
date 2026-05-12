package kotlinx.coroutines.slf4j

import kotlinx.coroutines.testing.*
import org.junit.Test
import kotlin.test.*

class MDCContextPlusOperatorTest : TestBase() {
    @Test
    fun testPlusMap() {
        assertEquals(
            mapOf("a" to "1"),
            (MDCContext() + mapOf("a" to "1")).contextMap,
        )
        assertEquals(
            mapOf("a" to "1", "b" to "2"),
            (MDCContext() + mapOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "value", "a" to "1", "b" to "2"),
            (MDCContext(mapOf("key" to "value")) + mapOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "new", "other" to "x"),
            (MDCContext(mapOf("key" to "value", "other" to "x")) + mapOf("key" to "new")).contextMap,
        )
        assertEquals(
            emptyMap(),
            (MDCContext() + emptyMap()).contextMap,
        )
    }

    @Test
    fun testPlusPair() {
        assertEquals(
            mapOf("a" to "1"),
            (MDCContext() + ("a" to "1")).contextMap,
        )
        assertEquals(
            mapOf("a" to "1", "b" to "2"),
            (MDCContext() + ("a" to "1") + ("b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "value", "a" to "1"),
            (MDCContext(mapOf("key" to "value")) + ("a" to "1")).contextMap,
        )
        assertEquals(
            mapOf("key" to "new"),
            (MDCContext(mapOf("key" to "value")) + ("key" to "new")).contextMap,
        )
    }

    @Test
    fun testPlusIterable() {
        assertEquals(
            mapOf("a" to "1", "b" to "2"),
            (MDCContext() + listOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "value", "a" to "1", "b" to "2"),
            (MDCContext(mapOf("key" to "value")) + listOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "new", "b" to "2"),
            (MDCContext(mapOf("key" to "value")) + listOf("key" to "new", "b" to "2")).contextMap,
        )
        assertEquals(
            emptyMap(),
            (MDCContext() + emptyList()).contextMap,
        )
    }

    @Test
    fun testPlusSequence() {
        assertEquals(
            mapOf("a" to "1", "b" to "2"),
            (MDCContext() + sequenceOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "value", "a" to "1", "b" to "2"),
            (MDCContext(mapOf("key" to "value")) + sequenceOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "new", "b" to "2"),
            (MDCContext(mapOf("key" to "value")) + sequenceOf("key" to "new", "b" to "2")).contextMap,
        )
        assertEquals(
            emptyMap(),
            (MDCContext() + emptySequence()).contextMap,
        )
    }

    @Test
    fun testPlusArray() {
        assertEquals(
            mapOf("a" to "1", "b" to "2"),
            (MDCContext() + arrayOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "value", "a" to "1", "b" to "2"),
            (MDCContext(mapOf("key" to "value")) + arrayOf("a" to "1", "b" to "2")).contextMap,
        )
        assertEquals(
            mapOf("key" to "new", "b" to "2"),
            (MDCContext(mapOf("key" to "value")) + arrayOf("key" to "new", "b" to "2")).contextMap,
        )
        assertEquals(
            emptyMap(),
            (MDCContext() + emptyArray<Pair<String, String>>()).contextMap,
        )
    }
}
