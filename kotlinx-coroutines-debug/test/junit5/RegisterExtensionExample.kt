/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.*
import org.junit.jupiter.api.*
import org.junit.jupiter.api.extension.*

class RegisterExtensionExample {
    @JvmField
    @RegisterExtension
    internal val timeout = CoroutinesTimeoutExtension.seconds(5)

    @Test
    fun testThatHangs() = runBlocking {
        delay(Long.MAX_VALUE) // somewhere deep in the stack
    }
}