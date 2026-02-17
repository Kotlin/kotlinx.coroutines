@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class FlowCallbackTest : TestBase() {
    @Test
    fun testClosedPrematurely() = runTest {
        val outerScope = this
        val flow = callbackFlow {
            // ~ callback-based API
            outerScope.launch(Job()) {
                try {
                    expect(4)
                    send(1)
                    expectUnreached()
                } catch (e: IllegalStateException) {
                    expect(5)
                    assertTrue(e.message!!.contains("awaitClose"))
                }
                finish(6)
            }
            expect(1)
        }
        try {
            flow.collect()
        } catch (e: IllegalStateException) {
            expect(2)
            assertTrue(e.message!!.contains("awaitClose"))
        }
        expect(3)
    }

    @Test
    fun testNotClosedPrematurely() = runTest {
        val outerScope = this
        val flow = callbackFlow {
            // ~ callback-based API
            outerScope.launch(Job()) {
                expect(2)
                send(1)
                close()
            }
            expect(1)
            awaitClose()
        }

        assertEquals(listOf(1), flow.toList())
        finish(3)
    }
}
