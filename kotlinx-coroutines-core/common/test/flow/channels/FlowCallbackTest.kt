/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FlowCallbackTest : TestBase() {
    @Test
    fun testClosedPrematurely() = runTest {
        val outerScope = this
        val flow = callbackFlow {
            // ~ callback-based API
            outerScope.launch(Job()) {
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
