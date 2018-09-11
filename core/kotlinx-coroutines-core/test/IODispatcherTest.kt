/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.Test
import kotlin.test.*

class IODispatcherTest : TestBase() {
    @Test
    fun testWithIOContext() = runTest {
        // just a very basic test that is dispatcher works and indeed uses background thread
        val mainThread = Thread.currentThread()
        expect(1)
        withContext(Dispatchers.IO) {
            expect(2)
            assertNotSame(mainThread, Thread.currentThread())
        }
        expect(3)
        assertSame(mainThread, Thread.currentThread())
        finish(4)
    }
}