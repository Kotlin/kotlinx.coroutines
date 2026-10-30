package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

public actual typealias TestResult = Unit

internal actual fun systemPropertyImpl(name: String): String? = null

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit) =
    runTestCoroutine(EmptyCoroutineContext, testProcedure)

internal actual fun dumpCoroutines() { }
