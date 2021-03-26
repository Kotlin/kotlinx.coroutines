/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.*
import org.junit.jupiter.api.*

/**
 * This test checks that nested classes correctly recognize the [CoroutinesTimeout] annotation.
 *
 * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
 */
@CoroutinesTimeout(200)
class CoroutinesTimeoutNestedTest {
    @Nested
    inner class NestedInInherited {
        @Test
        fun usesOuterClassTimeout() = runBlocking {
            delay(1000)
        }

        @Test
        fun fitsInOuterClassTimeout() = runBlocking {
            delay(10)
        }
    }
}
