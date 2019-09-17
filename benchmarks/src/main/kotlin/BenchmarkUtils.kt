/*
* Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
*/

import java.util.concurrent.ThreadLocalRandom

fun doWork(work: Int) {
    // We use geometric distribution here
    val p = 1.0 / work
    val r = ThreadLocalRandom.current()
    while (true) {
        if (r.nextDouble() < p) break
    }
}