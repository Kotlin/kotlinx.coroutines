/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.basic03s

import kotlinx.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking { // this: CoroutineScope
    launch { // launch new coroutine in the scope of runBlocking
        delay(1000L)
        println("World!")
    }
    println("Hello,")
}
