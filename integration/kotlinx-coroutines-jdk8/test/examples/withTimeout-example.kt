/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.examples

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.future.*

fun main(args: Array<String>) {
    fun slow(s: String) = future {
        delay(500L)
        s
    }
    val f = future<String> {
        log("Started f")
        val a = slow("A").await()
        log("a = $a")
        withTimeout(1000L) {
            val b = slow("B").await()
            log("b = $b")
        }
        try {
            withTimeout(750L) {
                val c = slow("C").await()
                log("c = $c")
                val d = slow("D").await()
                log("d = $d")
            }
        } catch (ex: CancellationException) {
            log("timed out with $ex")
        }
        val e = slow("E").await()
        log("e = $e")
        "done"
    }
    log("f.get() = ${f.get()}")
}
