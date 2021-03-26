/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.*
import org.junit.jupiter.api.*

/**
 * Tests the basic usage of [CoroutinesTimeout] on classes and test methods.
 *
 * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
 */
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@CoroutinesTimeout(100)
class CoroutinesTimeoutSimpleTest {

    @Test
    @Order(1)
    fun usesClassTimeout1() {
        runBlocking {
            delay(150)
        }
    }

    @CoroutinesTimeout(1000)
    @Test
    @Order(2)
    fun ignoresClassTimeout() {
        runBlocking {
            delay(150)
        }
    }

    @CoroutinesTimeout(200)
    @Test
    @Order(3)
    fun usesMethodTimeout() {
        runBlocking {
            delay(300)
        }
    }

    @Test
    @Order(4)
    fun fitsInClassTimeout() {
        runBlocking {
            delay(50)
        }
    }

    @Test
    @Order(5)
    fun usesClassTimeout2() {
        runBlocking {
            delay(150)
        }
    }

}
