package kotlinx.coroutines.test

import kotlin.test.*

actual fun testResultChain(block: () -> TestResult, after: (Result<Unit>) -> TestResult): TestResult =
    block().then(
        {
            after(Result.success(Unit))
        }, {
            after(Result.failure(it))
        })

actual typealias NoJs = Ignore
