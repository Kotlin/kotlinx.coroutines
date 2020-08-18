/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class ImmediateDispatcherTest : TestBase() {

    @Test
    fun testImmediate() = runTest {
        expect(1)
        val job = launch { expect(3) }
        withContext(Dispatchers.Main.immediate) {
            expect(2)
        }
        job.join()
        finish(4)
    }

    @Test
    fun testMain() = runTest {
        expect(1)
        val job = launch { expect(2) }
        withContext(Dispatchers.Main) {
            expect(3)
        }
        job.join()
        finish(4)
    }
}
