/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class SelectLinkedListChannelTest : TestBase() {
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