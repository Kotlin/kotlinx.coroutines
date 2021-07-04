/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.time.*
import java.util.concurrent.atomic.*
import kotlin.time.*

@OptIn(ExperimentalTime::class)
internal class TestNanoTimeSource : NanoTimeSource() {
    @Volatile
    var nanos:Long = 0L
    override fun markNow(): NanoTimeMark = NanoTimeMark(nanos, this)
}
internal class Delayer {
    private val delayCounter = AtomicLong(0)
    fun delay(duration: Long){
        delayCounter.addAndGet(duration)
    }
    public fun getDelay():Long = delayCounter.get()
    public fun reset():Unit = delayCounter.set(0)
}
