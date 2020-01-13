/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks.common

import java.util.concurrent.*

fun doGeomDistrWork(work: Int) {
    // We use geometric distribution here. We also checked on macbook pro 13" (2017) that the resulting work times
    // are distributed geometrically, see https://github.com/Kotlin/kotlinx.coroutines/pull/1464#discussion_r355705325
    val p = 1.0 / work
    val r = ThreadLocalRandom.current()
    while (true) {
        if (r.nextDouble() < p) break
    }
}