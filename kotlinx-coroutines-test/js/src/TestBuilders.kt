/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.js.*

public actual class TestResult internal constructor(executor: ((Unit) -> Unit, (Throwable) -> Unit) -> Unit) :
    Promise<Unit>(executor) {
    internal fun then(
        onFulfilled: (Unit) -> TestResult,
        onRejected: (Throwable) -> TestResult
    ): TestResult = GlobalScope.async {
        val result = runCatching { this@TestResult.asDeferred().await() }
        if (result.isSuccess) {
            onFulfilled(Unit)
        } else {
            onRejected(result.exceptionOrNull()!!)
        }.await()
    }.asPromiseOfUnit()
}

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit): TestResult =
    GlobalScope.async {
        testProcedure()
    }.asPromiseOfUnit()

/** copy-pasted from [Deferred.asPromise] */
private fun Deferred<Unit>.asPromiseOfUnit(): TestResult {
    val promise = TestResult { resolve, reject ->
        invokeOnCompletion {
            val e = getCompletionExceptionOrNull()
            if (e != null) {
                reject(e)
            } else {
                resolve(getCompleted())
            }
        }
    }
    promise.asDynamic().deferred = this
    return promise
}

internal actual fun dumpCoroutines() {}
