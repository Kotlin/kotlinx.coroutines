/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.examples

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.future.*
import java.util.concurrent.*

fun main(args: Array<String>)  {
    log("Started")
    val deferred = GlobalScope.async {
        log("Busy...")
        delay(1000)
        log("Done...")
        42
    }
    val future = deferred.asCompletableFuture()
    log("Got ${future.get()}")
}


