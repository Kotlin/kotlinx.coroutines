package kotlinx.coroutines.internal

import kotlinx.coroutines.testing.*
import junit.framework.Assert.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.*

class ConcurrentWeakMapTest : TestBase() {
    @Test
    fun testSimple() {
        val expect = (1..1000).associate { it.toString().let { it to it } }
        val m = ConcurrentWeakMap<String, String>()
        // repeat adding/removing a few times
        repeat(5) {
            assertEquals(0, m.size)
            assertEquals(emptySet<Int>(), m.keys)
            assertEquals(emptyList<String>(), m.values.toList())
            assertEquals(emptySet<Map.Entry<Int, String>>(), m.entries)
            for ((k, v) in expect) {
                assertNull(m.put(k, v))
            }
            assertEquals(expect.size, m.size)
            assertEquals(expect.keys, m.keys)
            assertEquals(expect.entries, m.entries)
            for ((k, v) in expect) {
                assertEquals(v, m[k])
            }
            assertEquals(expect.size, m.size)
            if (it % 2 == 0) {
                for ((k, v) in expect) {
                    assertEquals(v, m.remove(k))
                }
            } else {
                m.clear()
            }
            assertEquals(0, m.size)
            for ((k, _) in expect) {
                assertNull(m[k])
            }
        }
    }
}
