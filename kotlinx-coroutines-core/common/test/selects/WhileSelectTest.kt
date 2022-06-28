/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class WhileSelectTest : TestBase() {

    @Test
    fun testSimple() = runTest {
        val c = Channel<Int>(3)
        assertTrue(c.trySend(1).isSuccess)
        assertTrue(c.trySend(2).isSuccess)
        assertTrue(c.trySend(3).isSuccess)
        var element = 1
        whileSelect {
            c.onReceive {
                assertEquals(it, element++)
                element == 4
            }
        }
    }
}