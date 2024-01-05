package kotlinx.coroutines.jdk9

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class PublisherMultiTest : TestBase() {
    @Test
    fun testConcurrentStress() = runBlocking {
        val n = 10_000 * stressTestMultiplier
        val observable = flowPublish {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch {
                    send(it)
                }
            }
            jobs.forEach { it.join() }
        }
        val resultSet = mutableSetOf<Int>()
        observable.collect {
            assertTrue(resultSet.add(it))
        }
        assertEquals(n, resultSet.size)
    }
}
