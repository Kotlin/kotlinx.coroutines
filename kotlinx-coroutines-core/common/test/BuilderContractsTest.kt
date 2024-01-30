package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import kotlin.test.*

class BuilderContractsTest : TestBase() {

    @Test
    fun testContracts() = runTest {
        // Coroutine scope
        val cs: Int
        coroutineScope {
            cs = 42
        }
        consume(cs)

        // Supervisor scope
        val svs: Int
        supervisorScope {
            svs = 21
        }
        consume(svs)

        // with context scope
        val wctx: Int
        withContext(Dispatchers.Unconfined) {
            wctx = 239
        }
        consume(wctx)

        val wt: Int
        withTimeout(Long.MAX_VALUE) {
            wt = 123
        }
        consume(wt)

        val s: Int
        select<Unit> {
            s = 42
            Job().apply { complete() }.onJoin {}
        }
        consume(s)


        val ch: Int
        val i = Channel<Int>()
        i.consume {
            ch = 321
        }
        consume(ch)
    }

    private fun consume(a: Int) {
        /*
         * Verify the value is actually set correctly
         * (non-zero, VerificationError is not triggered, can be read)
         */
        assertNotEquals(0, a)
        assertEquals(a.hashCode(), a)
    }
}
