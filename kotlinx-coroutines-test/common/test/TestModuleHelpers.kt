/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlin.test.*
import kotlin.time.*

/**
 * The number of milliseconds that is sure not to pass [assertRunsFast].
 */
const val SLOW = 100_000L

/**
 * Asserts that a block completed within [timeout].
 */
@OptIn(ExperimentalTime::class)
inline fun <T> assertRunsFast(timeout: Duration, block: () -> T): T {
    val result: T
    val elapsed = TimeSource.Monotonic.measureTime { result = block() }
    assertTrue("Should complete in $timeout, but took $elapsed") { elapsed < timeout }
    return result
}

/**
 * Asserts that a block completed within two seconds.
 */
@OptIn(ExperimentalTime::class)
inline fun <T> assertRunsFast(block: () -> T): T = assertRunsFast(Duration.seconds(2), block)
