package benchmarks

import java.util.concurrent.TimeUnit
import kotlin.coroutines.*
import kotlinx.coroutines.*
import org.openjdk.jmh.annotations.*

private class E1 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E1>
}

private class E2 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E2>
}

private class E3 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E3>
}

private class E4 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E4>
}

private class E5 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E5>
}

private class E6 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E6>
}

private class E7 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E7>
}

private class E8 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E8>
}

private class E9 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E9>
}

private class E10 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E10>
}

private class E11 : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<E11>
}

private class CTCE1 : AbstractCoroutineContextElement(Key), CopyableThreadContextElement<Unit> {
    companion object Key : CoroutineContext.Key<CTCE1>
    override fun updateThreadContext(context: CoroutineContext) {}
    override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {}
    override fun copyForChild() = CTCE1()
    override fun mergeForChild(overwritingElement: CoroutineContext.Element) = CTCE1()
}

private class CTCE2 : AbstractCoroutineContextElement(Key), CopyableThreadContextElement<Unit> {
    companion object Key : CoroutineContext.Key<CTCE2>
    override fun updateThreadContext(context: CoroutineContext) {}
    override fun restoreThreadContext(context: CoroutineContext, oldState: Unit) {}
    override fun copyForChild() = CTCE2()
    override fun mergeForChild(overwritingElement: CoroutineContext.Element) = CTCE2()
}

/**
 * Distinct execution scenarios representing the key code paths across the various
 * [CoroutineContext] fold implementations.
 */
enum class Scenario(val originalContext: CoroutineContext, val appendContext: CoroutineContext) {
    /**
     * The LHS context contains only regular elements, and the RHS appended context is
     * [EmptyCoroutineContext]. Exercises fast-paths when appending an empty context to a standard
     * context without [CopyableThreadContextElement]s.
     */
    PLUS_EMPTY(E1() + E2() + E3() + E4() + E5() + E6() + E7() + E8() + E9() + E10(), EmptyCoroutineContext),

    /**
     * Neither the LHS nor the RHS context contains any [CopyableThreadContextElement]s. Exercises the
     * standard baseline coroutine context addition without thread-local element copying.
     */
    PLUS_E(E1() + E2() + E3() + E4() + E5() + E6() + E7() + E8() + E9() + E10(), E11()),

    /**
     * The RHS context contains new [CopyableThreadContextElement] keys that are not present in the
     * LHS context. Exercises the [CopyableThreadContextElement.copyForChild] code path for newly
     * introduced elements.
     */
    PLUS_CTCE(E1() + E2() + E3() + E4() + E5() + E6() + E7() + E8() + E9() + E10(), CTCE1()),

    /**
     * The LHS context contains [CopyableThreadContextElement]s, but the RHS appended context is
     * [EmptyCoroutineContext]. Exercises fast-paths that avoid context traversals or allocations when
     * appending an empty context.
     */
    CTCE_PLUS_EMPTY(E1() + E2() + E3() + E4() + E5() + E6() + CTCE1() + E8() + E9() + E10(), EmptyCoroutineContext),

    /**
     * The LHS context contains [CopyableThreadContextElement]s, but the RHS context contains only
     * regular elements. Exercises fast-paths where existing copyable elements do not need to be
     * merged or overridden.
     */
    CTCE_PLUS_E(E1() + E2() + E3() + E4() + E5() + E6() + CTCE1() + E8() + E9() + E10(), E11()),

    /**
     * Both LHS and RHS contexts contain [CopyableThreadContextElement]s with distinct keys (no
     * merge). Exercises copying existing LHS copyable elements while simultaneously copying and
     * appending new RHS copyable elements.
     */
    CTCE_PLUS_CTCE(E1() + E2() + E3() + E4() + E5() + E6() + CTCE1() + E8() + E9() + E10(), CTCE2()),

    /**
     * Both LHS and RHS contexts contain [CopyableThreadContextElement]s that share the same key,
     * where the element in LHS is located at the earliest (deepest) position in the context chain.
     *
     * Exercises worst-case traversal for [CopyableThreadContextElement.mergeForChild], contrasting
     * with the O(1) tail lookup in [MERGE_TAIL].
     */
    MERGE_HEAD(CTCE1() + E2() + E3() + E4() + E5() + E6() + E7() + E8() + E9() + E10(), CTCE1()),

    /**
     * Both LHS and RHS contexts contain [CopyableThreadContextElement]s with the same key, where the
     * element in LHS is located at the rightmost tail of the context chain.
     *
     * Because right-to-left key lookups in [CombinedContext] check the newest element first, this
     * exercises the O(1) lookup path during merging (contrasting with [MERGE_HEAD]). This also
     * reflects the steady-state performance of subsequent child coroutine launches after an initial
     * merge moves the element to the tail.
     */
    MERGE_TAIL(E1() + E2() + E3() + E4() + E5() + E6() + E7() + E8() + E9() + CTCE1(), CTCE1()),
}

/** Benchmark suite evaluating implementations of merging and folding coroutine contexts. */
@Fork(1)
@Warmup(iterations = 8, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@BenchmarkMode(Mode.AverageTime)
@State(Scope.Benchmark)
open class CoroutineContextMergingBenchmark {

    @Param lateinit var scenario: Scenario

    private lateinit var scope: CoroutineScope

    @Setup
    fun setup() {
        scope = CoroutineScope(scenario.originalContext)
    }

    @Benchmark
    fun rawPlus(): CoroutineContext = scenario.originalContext + scenario.appendContext

    @OptIn(InternalCoroutinesApi::class)
    @Benchmark
    fun withContext(): CoroutineContext =
        scenario.originalContext.newCoroutineContext(scenario.appendContext)

    @OptIn(ExperimentalCoroutinesApi::class)
    @Benchmark
    fun launch(): CoroutineContext =
        scope.newCoroutineContext(scenario.appendContext)
}
