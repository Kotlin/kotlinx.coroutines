/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

/**
 * Runs [test], and then invokes [block], passing to it the lambda that functionally behaves
 * the same way [test] does.
 */
fun testResultMap(block: (() -> Unit) -> Unit, test: () -> TestResult): TestResult = testResultChain(
    block = test,
    after = {
        block { it.getOrThrow() }
        createTestResult { }
    }
)

/**
 * Chains together [block] and [after], passing the result of [block] to [after].
 */
expect fun testResultChain(block: () -> TestResult, after: (Result<Unit>) -> TestResult): TestResult

fun testResultChain(vararg chained: (Result<Unit>) -> TestResult, initialResult: Result<Unit> = Result.success(Unit)): TestResult =
    if (chained.isEmpty()) {
        createTestResult {
            initialResult.getOrThrow()
        }
    } else {
        testResultChain(block = {
            chained[0](initialResult)
        }) {
            testResultChain(*chained.drop(1).toTypedArray(), initialResult = it)
        }
    }
