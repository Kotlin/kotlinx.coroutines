/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import kotlin.time.*

@SinceKotlin("1.5")
@ExperimentalTime
internal open class LongTimeSource : TimeSource {
    override fun markNow(): LongTimeMark = LongTimeMark(nanoTime(), this)
}

@SinceKotlin("1.5")
@OptIn(ExperimentalTime::class)
internal class LongTimeMark(private val nanos: Long, private val source: LongTimeSource) : TimeMark() {

    operator fun minus(other: LongTimeMark): Duration = Duration.nanoseconds(nanos - other.nanos)
    override operator fun minus(duration: Duration): LongTimeMark =
        LongTimeMark(nanos - duration.inWholeNanoseconds, source)

    override operator fun plus(duration: Duration): LongTimeMark =
        LongTimeMark(nanos + duration.inWholeNanoseconds, source)

    override fun elapsedNow(): Duration = source.markNow() - this
    operator fun compareTo(other: LongTimeMark): Int = nanos.compareTo(other.nanos)
}
