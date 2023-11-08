/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test
import kotlinx.coroutines.*
import kotlin.js.*

@JsName("Promise")
public external class MyPromise {
    public fun then(onFulfilled: ((Unit) -> Unit), onRejected: ((Throwable) -> Unit)): MyPromise
    public fun then(onFulfilled: ((Unit) -> Unit)): MyPromise
}

@Suppress("EXPECT_ACTUAL_CLASSIFIERS_ARE_IN_BETA_WARNING")
public actual typealias TestResult = MyPromise

@Suppress("CAST_NEVER_SUCCEEDS") // 'external' + JsName false-positive suppress
internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit): TestResult =
    GlobalScope.promise {
        testProcedure()
    } as MyPromise

internal actual fun dumpCoroutines() { }
