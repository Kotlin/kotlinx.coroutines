/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*

@Suppress("ACTUAL_WITHOUT_EXPECT")
public actual typealias TestResult = Unit

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit) {
    runBlocking {
        testProcedure()
    }
}

internal actual fun getLastKnownPosition(): Any? = Thread.currentThread()

internal actual fun dumpCoroutinesAndThrow(exception: Throwable, lastKnownPosition: Any?) {
    val thread = lastKnownPosition as? Thread
    @Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
    if (DebugProbesImpl.isInstalled) {
        DebugProbesImpl.install()
        try {
            DebugProbesImpl.dumpCoroutines(System.err)
            System.err.flush()
        } finally {
            DebugProbesImpl.uninstall()
        }
    }
    thread?.stackTrace?.let { exception.stackTrace = it }
    throw exception
}
