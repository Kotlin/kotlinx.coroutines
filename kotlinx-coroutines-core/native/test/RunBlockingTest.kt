/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines
import kotlin.test.*

class RunBlockingTest : TestBase() {

    @Test
    fun testIncompleteState() {
        val handle = runBlocking {
            coroutineContext[Job]!!.invokeOnCompletion { }
        }

        handle.dispose()
    }
}