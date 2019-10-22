/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class AsyncJvmTest : TestBase() {
    // This must be a common test but it fails on JS because of KT-21961
    suspend fun test() {
        println("test.begin")
        delay(5000)
        println("test.end")
    }

    suspend fun proxy() {
        println("?")
        test()
        println("?")
    }

//    @Test
    fun main() {
        println("AA")
        runBlocking {
            withTimeout(100) {
                proxy()
                println()
            }
            println()
        }
    }
}
