/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import kotlin.time.*

internal interface NanoTimeSource {
    fun markNow(): NanoTimeMark
}

@SinceKotlin("1.5")
@ExperimentalTime
internal object NanoTimeSourceImpl : NanoTimeSource {
    override fun markNow(): NanoTimeMark = NanoTimeMark(nanoTime(), this)
}

@SinceKotlin("1.5")
@OptIn(ExperimentalTime::class)
internal class NanoTimeMark(val nanos: Long, private val source: NanoTimeSource) : TimeMark() {
    companion object {
        /**
         * Long.MAX_VALUE used as nanos, converted to days, is still more than 100_000 days (still only half of the span).
         * 0.1% of that is 100 days. And the borderland of 99.88% is vast. Good enough for close to real.
         */
        private const val upper_edge = Long.MAX_VALUE * 0.999
        private const val lower_edge = Long.MIN_VALUE * 0.999
    }

    /**
     * Difference between two points in time, Duration is negative if other is larger
     */
    operator fun minus(other: NanoTimeMark): Duration = when {
        nanos > upper_edge && other.nanos < lower_edge -> Duration.nanoseconds(-1L - (other.nanos - Long.MIN_VALUE) - (Long.MAX_VALUE - nanos))
        nanos < lower_edge && other.nanos > upper_edge -> Duration.nanoseconds(1L + (nanos - Long.MIN_VALUE) + (Long.MAX_VALUE - other.nanos))
        else -> Duration.nanoseconds(nanos - other.nanos)
    }

    /**
     * Subtract duration from Time mark
     */
    override operator fun minus(duration: Duration): NanoTimeMark = when {
        nanos < lower_edge && nanos - Long.MIN_VALUE < duration.inWholeNanoseconds -> {
            NanoTimeMark(Long.MAX_VALUE - duration.inWholeNanoseconds + nanos - Long.MIN_VALUE, source)
        }
        else -> NanoTimeMark(nanos - duration.inWholeNanoseconds, source)
    }

    /**
     * Add duration to time mark
     */
    override operator fun plus(duration: Duration): NanoTimeMark = when {
        nanos > upper_edge && Long.MAX_VALUE - nanos < duration.inWholeNanoseconds -> {
            NanoTimeMark(Long.MIN_VALUE + duration.inWholeNanoseconds - (Long.MAX_VALUE - nanos), source)
        }
        else -> NanoTimeMark(nanos + duration.inWholeNanoseconds, source)
    }

    override fun elapsedNow(): Duration = source.markNow() - this
    operator fun compareTo(other: NanoTimeMark): Int = when {
        nanos < lower_edge && other.nanos > upper_edge -> 1
        else -> nanos.compareTo(other.nanos)
    }
}
