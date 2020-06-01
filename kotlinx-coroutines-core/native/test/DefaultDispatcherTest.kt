/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class DefaultDispatcherTest : TestBase() {
    private val testThread = currentThread()

    @Test
    fun testDefaultDispatcher() = runTest {
        expect(1)
        withContext(Dispatchers.Default) {
            assertTrue(currentThread() != testThread)
            expect(2)
        }
        assertEquals(testThread, currentThread())
        finish(3)
    }
}