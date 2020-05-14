/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class CancellableTest : TestBase() {

    @Test
    fun testCancellable() = runTest {
        var sum = 0
        val flow = (0..1000).asFlow()
            .onEach {
                if (it != 0) currentContext().cancel()
                sum += it
            }

        flow.launchIn(this).join()
        assertEquals(500500, sum)
        
        sum = 0
        flow.cancellable().launchIn(this).join()
        assertEquals(1, sum)
    }
}