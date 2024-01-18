package kotlinx.coroutines.test

import kotlin.test.*

actual fun testResultChain(block: () -> TestResult, after: (Result<Unit>) -> TestResult): TestResult {
    try {
        block()
        after(Result.success(Unit))
    } catch (e: Throwable) {
        after(Result.failure(e))
    }
}

actual typealias NoNative = Ignore
