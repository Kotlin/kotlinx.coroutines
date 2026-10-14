package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*
import kotlin.coroutines.CoroutineContext
import kotlin.js.*

public actual typealias TestResult = JsPromiseInterfaceForTesting

@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit): TestResult =
    GlobalScope.promise {
        testProcedure()
        Unit.toJsReference()
    }.unsafeCast()

internal actual fun dumpCoroutines() { }

internal actual fun systemPropertyImpl(name: String): String? = null

internal actual fun testCancellingDispatcher(): CloseableCoroutineDispatcher = closeableDefaultDispatcherWrapper

private val closeableDefaultDispatcherWrapper = object: CloseableCoroutineDispatcher() {
    override fun close() { }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        Dispatchers.Default.dispatch(context, block)
    }
}
