@file:OptIn(ExperimentalStdlibApi::class)

package kotlinx.coroutines

import kotlinx.coroutines.scheduling.CORE_POOL_SIZE
import kotlinx.coroutines.scheduling.MAX_POOL_SIZE
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
        for (parallelism in 1..100) {
            assertEquals(
                "Dispatchers.IO" + if (parallelism < MAX_POOL_SIZE) ".limitedParallelism($parallelism)" else "",
                Dispatchers.IO.limitedParallelism(parallelism).toString()
            )
            assertEquals(
                "Dispatchers.Default" + if (parallelism < CORE_POOL_SIZE) ".limitedParallelism($parallelism)" else "",
                Dispatchers.Default.limitedParallelism(parallelism).toString()
            )
        }
        // Not overridden at all, limited parallelism returns `this`
        assertEquals("DefaultExecutor", (DefaultDelay as CoroutineDispatcher).limitedParallelism(42).toString())

        assertEquals("filesDispatcher", Dispatchers.IO.limitedParallelism(1, "filesDispatcher").toString())
        assertEquals("json", Dispatchers.Default.limitedParallelism(2, "json").toString())
        assertEquals("\uD80C\uDE11", (DefaultDelay as CoroutineDispatcher).limitedParallelism(42, "\uD80C\uDE11").toString())
        assertEquals("DefaultExecutor", (DefaultDelay as CoroutineDispatcher).limitedParallelism(42).toString())

        val limitedNamed = Dispatchers.IO.limitedParallelism(10, "limited")
        assertEquals("limited.limitedParallelism(2)", limitedNamed.limitedParallelism(2).toString())
        assertEquals("2", limitedNamed.limitedParallelism(2, "2").toString())
        // We asked for too many threads with no name, this was returned
        assertEquals("limited", limitedNamed.limitedParallelism(12).toString())
        assertEquals("12", limitedNamed.limitedParallelism(12, "12").toString())

        runBlocking {
            val d = coroutineContext[CoroutineDispatcher]!!
            assertContains(d.toString(), "BlockingEventLoop")
            val limited = d.limitedParallelism(2)
            assertContains(limited.toString(), "BlockingEventLoop")
            assertFalse(limited.toString().contains("limitedParallelism"))
            val named = d.limitedParallelism(2, "Named")
            assertEquals("Named", named.toString())
        }
    }
}