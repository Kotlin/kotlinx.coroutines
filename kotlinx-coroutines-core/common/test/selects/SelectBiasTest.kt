package kotlinx.coroutines.selects

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class SelectBiasTest : TestBase() {
    val n = 10_000

    @Test
    fun testBiased() = runTest {
        val d0 = async { 0 }
        val d1 = async { 1 }
        val counter = IntArray(2)
        repeat(n) {
            val selected = select<Int> {
                d0.onAwait { 0 }
                d1.onAwait { 1 }
            }
            counter[selected]++
        }
        assertEquals(n, counter[0])
        assertEquals(0, counter[1])
    }

    @Test
    fun testUnbiased() = runTest {
        val d0 = async { 0 }
        val d1 = async { 1 }
        val counter = IntArray(2)
        repeat(n) {
            val selected = selectUnbiased<Int> {
                d0.onAwait { 0 }
                d1.onAwait { 1 }
            }
            counter[selected]++
        }
        assertTrue(counter[0] >= n / 4)
        assertTrue(counter[1] >= n / 4)
    }
}