package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*

public actual typealias TestResult = JsPromiseInterfaceForTesting


@Suppress("CAST_NEVER_SUCCEEDS")
internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit): TestResult =
    GlobalScope.promise {
        testProcedure()
    } as JsPromiseInterfaceForTesting

internal actual fun dumpCoroutines() { }

internal actual fun systemPropertyImpl(name: String): String? = null
