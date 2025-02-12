package kotlinx.coroutines

import java.util.concurrent.*

public fun doGeomDistrWork(work: Int) {
    // We use geometric distribution here. We also checked on macbook pro 13" (2017) that the resulting work times
    // are distributed geometrically, see https://github.com/Kotlin/kotlinx.coroutines/pull/1464#discussion_r355705325
    val p = 1.0 / work
    val r = ThreadLocalRandom.current()
    while (true) {
        if (r.nextDouble() < p) break
    }
}
