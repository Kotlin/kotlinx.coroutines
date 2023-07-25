/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*

public actual typealias TestResult = JsPromiseInterfaceForTesting

internal actual fun systemPropertyImpl(name: String): String? = null

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit): TestResult =
    GlobalScope.promise {
        testProcedure()
    } as JsPromiseInterfaceForTesting

internal actual fun dumpCoroutines() {}
