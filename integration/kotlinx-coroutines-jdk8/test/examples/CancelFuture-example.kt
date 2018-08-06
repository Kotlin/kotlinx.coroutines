/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.examples

import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.future.future


fun main(args: Array<String>) {
    val f = future {
        try {
            log("Started f")
            delay(500)
            log("Slept 500 ms #1")
            delay(500)
            log("Slept 500 ms #2")
            delay(500)
            log("Slept 500 ms #3")
            delay(500)
            log("Slept 500 ms #4")
            delay(500)
            log("Slept 500 ms #5")
        } catch(e: Exception) {
            log("Aborting because of $e")
        }
    }
    Thread.sleep(1200)
    f.cancel(false)
}