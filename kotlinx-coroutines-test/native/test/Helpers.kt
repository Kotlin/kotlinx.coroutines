/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

actual fun testResultChain(block: () -> TestResult, after: (Result<Unit>) -> TestResult): TestResult {
    try {
        block()
        after(Result.success(Unit))
    } catch (e: Throwable) {
        after(Result.failure(e))
    }
}
