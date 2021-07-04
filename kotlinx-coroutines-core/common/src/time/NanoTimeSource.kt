/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import kotlin.time.*

@SinceKotlin("1.5")
@ExperimentalTime
internal open class NanoTimeSource : TimeSource {
    override fun markNow(): NanoTimeMark = NanoTimeMark(nanoTime(), this)
}

@SinceKotlin("1.5")
@OptIn(ExperimentalTime::class)
internal class NanoTimeMark(private val nanos: Long, private val source: NanoTimeSource) : TimeMark() {

    operator fun minus(other: NanoTimeMark): Duration = Duration.nanoseconds(nanos - other.nanos)
    override operator fun minus(duration: Duration): NanoTimeMark =
        NanoTimeMark(nanos - duration.inWholeNanoseconds, source)

    override operator fun plus(duration: Duration): NanoTimeMark =
        NanoTimeMark(nanos + duration.inWholeNanoseconds, source)

    override fun elapsedNow(): Duration = source.markNow() - this
    operator fun compareTo(other: NanoTimeMark): Int = nanos.compareTo(other.nanos)
}
