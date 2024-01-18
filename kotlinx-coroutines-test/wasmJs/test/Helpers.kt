package kotlinx.coroutines.test

import kotlin.test.*

actual fun testResultChain(block: () -> TestResult, after: (Result<Unit>) -> TestResult): TestResult =
    block().then(
        {
            after(Result.success(Unit))
            null
        }, {
            after(Result.failure(it.toThrowableOrNull() ?: Throwable("Unexpected non-Kotlin exception $it")))
            null
        })

actual typealias NoJs = Ignore