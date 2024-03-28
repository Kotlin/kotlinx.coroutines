/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

@Suppress("ACTUAL_WITHOUT_EXPECT")
public actual typealias TestResult = Unit

internal actual fun systemPropertyImpl(name: String): String? = null

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit) =
    runTestCoroutine(EmptyCoroutineContext, testProcedure)

internal actual fun dumpCoroutines() { }