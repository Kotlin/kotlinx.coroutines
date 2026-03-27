package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FlowCallbackTest : TestBase() {
    @Test
    fun testClosedPrematurely() = runTest {
        val childScope = CoroutineScope(coroutineContext + Job())
        val flow = callbackFlow {
            // ~ callback-based API
            childScope.launch {
                expect(2)
                try {
                    send(1)
                    expectUnreached()
                } catch (e: IllegalStateException) {
                    expect(3)
                    assertTrue(e.message!!.contains("awaitClose"))
                }
            }
            expect(1)
        }
        try {
            flow.collect()
        } catch (e: IllegalStateException) {
            expect(4)
            assertTrue(e.message!!.contains("awaitClose"))
        }
        finish(5)
    }

    @Test
    fun testNotClosedPrematurely() = runTest {
        val childScope = CoroutineScope(coroutineContext + Job())
        val flow = callbackFlow {
            // ~ callback-based API
            childScope.launch {
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
