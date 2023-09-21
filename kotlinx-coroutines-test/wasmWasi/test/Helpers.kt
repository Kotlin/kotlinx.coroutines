package kotlinx.coroutines.test

actual fun testResultChain(block: () -> TestResult, after: (Result<Unit>) -> TestResult): TestResult {
    try {
        block()
        after(Result.success(Unit))
    } catch (e: Throwable) {
        after(Result.failure(e))
    }
}
