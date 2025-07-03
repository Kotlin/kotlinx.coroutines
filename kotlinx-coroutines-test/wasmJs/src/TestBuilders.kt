package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*
import kotlin.js.*

public actual typealias TestResult = JsPromiseInterfaceForTesting

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit): TestResult =
    GlobalScope.promise {
        testProcedure()
    }.unsafeCast()

internal actual fun dumpCoroutines() { }

internal actual fun systemPropertyImpl(name: String): String? = null
