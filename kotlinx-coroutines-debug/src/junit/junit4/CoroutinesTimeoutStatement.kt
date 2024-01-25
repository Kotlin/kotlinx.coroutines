package kotlinx.coroutines.debug.junit4

import kotlinx.coroutines.debug.*
import org.junit.runner.*
import org.junit.runners.model.*
import java.util.concurrent.*

internal class CoroutinesTimeoutStatement(
    private val testStatement: Statement,
    private val testDescription: Description,
    private val testTimeoutMs: Long,
    private val cancelOnTimeout: Boolean = false
) : Statement() {

    override fun evaluate() {
        try {
            runWithTimeoutDumpingCoroutines(testDescription.methodName, testTimeoutMs, cancelOnTimeout,
                { TestTimedOutException(testTimeoutMs, TimeUnit.MILLISECONDS) })
            {
                testStatement.evaluate()
            }
        } finally {
            DebugProbes.uninstall()
        }
    }
}
