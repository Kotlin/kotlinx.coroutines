package kotlinx.coroutines.selects

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class SelectUnlimitedChannelTest : TestBase() {
    @Test
    fun testSelectSendWhenClosed() = runTest {
        expect(1)
        val c = Channel<Int>(Channel.UNLIMITED)
        c.send(1) // enqueue buffered element
        c.close() // then close
        assertFailsWith<ClosedSendChannelException> {
            // select sender should fail
            expect(2)
            select {
                c.onSend(2) {
                    expectUnreached()
                }
            }
        }
        finish(3)
    }
}