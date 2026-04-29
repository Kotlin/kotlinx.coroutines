package kotlinx.coroutines.slf4j

import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import org.slf4j.*
import kotlin.test.*

@RunWith(Parameterized::class)
class MDCContextPlusOperatorTest(
    private val description: String,
    private val operation: () -> MDCContext,
    private val expectedContextMap: Map<String, String>
) {
    @Before
    fun setUp() {
        MDC.clear()
    }

    @After
    fun tearDown() {
        MDC.clear()
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun data(): List<Array<out Any>> = listOf(
            // ── Map overload ──────────────────────────────────────────────────────────
            arrayOf(
                "MDCContext() + single-entry map",
                { MDCContext() + mapOf("a" to "1") },
                mapOf("a" to "1")
            ),
            arrayOf(
                "MDCContext() + multi-entry map",
                { MDCContext() + mapOf("a" to "1", "b" to "2") },
                mapOf("a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + map adds new keys",
                { MDCContext(mapOf("key" to "value")) + mapOf("a" to "1", "b" to "2") },
                mapOf("key" to "value", "a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + map overrides shared key",
                { MDCContext(mapOf("key" to "value", "other" to "x")) + mapOf("key" to "new") },
                mapOf("key" to "new", "other" to "x")
            ),
            arrayOf(
                "MDCContext() + empty map",
                { MDCContext() + emptyMap() },
                emptyMap<String, String>()
            ),

            // ── Pair overload ─────────────────────────────────────────────────────────
            arrayOf(
                "MDCContext() + Pair",
                { MDCContext() + ("a" to "1") },
                mapOf("a" to "1")
            ),
            arrayOf(
                "MDCContext() + Pair + Pair",
                { MDCContext() + ("a" to "1") + ("b" to "2") },
                mapOf("a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + Pair adds new key",
                { MDCContext(mapOf("key" to "value")) + ("a" to "1") },
                mapOf("key" to "value", "a" to "1")
            ),
            arrayOf(
                "MDCContext(existing) + Pair overrides existing key",
                { MDCContext(mapOf("key" to "value")) + ("key" to "new") },
                mapOf("key" to "new")
            ),

            // ── Iterable overload ─────────────────────────────────────────────────────
            arrayOf(
                "MDCContext() + Iterable<Pair>",
                { MDCContext() + listOf("a" to "1", "b" to "2") },
                mapOf("a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + Iterable<Pair> adds new keys",
                { MDCContext(mapOf("key" to "value")) + listOf("a" to "1", "b" to "2") },
                mapOf("key" to "value", "a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + Iterable<Pair> overrides shared key",
                { MDCContext(mapOf("key" to "value")) + listOf("key" to "new", "b" to "2") },
                mapOf("key" to "new", "b" to "2")
            ),
            arrayOf(
                "MDCContext() + empty Iterable",
                { MDCContext() + emptyList() },
                emptyMap<String, String>()
            ),

            // ── Sequence overload ─────────────────────────────────────────────────────
            arrayOf(
                "MDCContext() + Sequence<Pair>",
                { MDCContext() + sequenceOf("a" to "1", "b" to "2") },
                mapOf("a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + Sequence<Pair> adds new keys",
                { MDCContext(mapOf("key" to "value")) + sequenceOf("a" to "1", "b" to "2") },
                mapOf("key" to "value", "a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + Sequence<Pair> overrides shared key",
                { MDCContext(mapOf("key" to "value")) + sequenceOf("key" to "new", "b" to "2") },
                mapOf("key" to "new", "b" to "2")
            ),
            arrayOf(
                "MDCContext() + empty Sequence",
                { MDCContext() + emptySequence<Pair<String, String>>() },
                emptyMap<String, String>()
            ),

            // ── Array overload ────────────────────────────────────────────────────────
            arrayOf(
                "MDCContext() + Array<Pair>",
                { MDCContext() + arrayOf("a" to "1", "b" to "2") },
                mapOf("a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + Array<Pair> adds new keys",
                { MDCContext(mapOf("key" to "value")) + arrayOf("a" to "1", "b" to "2") },
                mapOf("key" to "value", "a" to "1", "b" to "2")
            ),
            arrayOf(
                "MDCContext(existing) + Array<Pair> overrides shared key",
                { MDCContext(mapOf("key" to "value")) + arrayOf("key" to "new", "b" to "2") },
                mapOf("key" to "new", "b" to "2")
            ),
            arrayOf(
                "MDCContext() + empty Array",
                { MDCContext() + emptyArray<Pair<String, String>>() },
                emptyMap<String, String>()
            ),
        )
    }

    @Test
    fun testPlusOperator() {
        val result = operation()
        assertEquals(expectedContextMap, result.contextMap)
    }
}
