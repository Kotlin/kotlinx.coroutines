package kotlinx.coroutines

import kotlin.test.*

class DispatchersToStringTest {
    @Test
    fun testStrings() {
        assertEquals("Dispatchers.Unconfined", Dispatchers.Unconfined.toString())
        assertEquals("Dispatchers.Default", Dispatchers.Default.toString())
        assertEquals("Dispatchers.IO", Dispatchers.IO.toString())
        assertEquals("Dispatchers.Main[missing]", Dispatchers.Main.toString())
        assertEquals("Dispatchers.Main[missing]", Dispatchers.Main.immediate.toString())
    }

    @Test
    fun testLimitedParallelism() {
        assertEquals("Dispatchers.IO.limitedParallelism(1)", Dispatchers.IO.limitedParallelism(1).toString())
        assertEquals("Dispatchers.Default.limitedParallelism(2)", Dispatchers.Default.limitedParallelism(2).toString())
        // Not overridden at all, limited parallelism returns `this`
        assertEquals("DefaultExecutor", (DefaultDelay as CoroutineDispatcher).limitedParallelism(42).toString())
    }
}