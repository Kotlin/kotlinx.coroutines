package kotlinx.coroutines.experimental

public expect open class TestBase constructor() {
    public val isStressTest: Boolean
    public val stressTestMultiplier: Int

    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public fun error(message: Any, cause: Throwable? = null): Nothing
    public fun expect(index: Int)
    public fun expectUnreached()
    public fun finish(index: Int)

    @Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
    public fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    )
}
