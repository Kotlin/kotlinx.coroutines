package kotlinx.coroutines.test

@OptIn(ExperimentalWasmJsInterop::class)
actual fun testResultChain(block: () -> TestResult, after: (Result<Unit>) -> TestResult): TestResult =
    block().then(
        {
            after(Result.success(Unit))
        }, {
            after(Result.failure(it.toThrowableOrNull() ?: Throwable("Unexpected non-Kotlin exception $it")))
        })
