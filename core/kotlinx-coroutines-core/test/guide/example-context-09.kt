/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.context09

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking<Unit> {
    launch(DefaultDispatcher + CoroutineName("test")) {
        println("I'm working in thread ${Thread.currentThread().name}")
    }
}
