/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling


internal class TestTimeSource(var time: Long) : SchedulerTimeSource() {

    override fun nanoTime() = time

    fun step(delta: Long = WORK_STEALING_TIME_RESOLUTION_NS) {
        time += delta
    }
}
