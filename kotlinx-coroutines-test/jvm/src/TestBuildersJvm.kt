package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*

public actual typealias TestResult = Unit

internal actual fun createTestResult(testProcedure: suspend CoroutineScope.() -> Unit) {
    runBlocking {
        testProcedure()
    }
}

internal actual fun systemPropertyImpl(name: String): String? =
    try {
        System.getProperty(name)
    } catch (e: SecurityException) {
        null
    }

internal actual fun dumpCoroutines() {
    @Suppress("INVISIBLE_REFERENCE")
    if (DebugProbesImpl.isInstalled) {
        DebugProbesImpl.install()
        try {
            DebugProbesImpl.dumpCoroutines(System.err)
            System.err.flush()
        } finally {
            DebugProbesImpl.uninstall()
        }
    }
}
