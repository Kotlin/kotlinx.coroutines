/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test
import kotlinx.coroutines.*
import kotlin.native.concurrent.*
import kotlinx.cinterop.*
import platform.posix.*

@Suppress("ACTUAL_WITHOUT_EXPECT")
public actual typealias TestResult = Unit

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit) {
    runBlocking {
        testProcedure()
    }
}

@OptIn(kotlinx.cinterop.ExperimentalForeignApi::class)
internal actual fun environmentVariableImpl(name: String): String? =
    getenv(name)?.toKString()

internal actual fun dumpCoroutines() { }
