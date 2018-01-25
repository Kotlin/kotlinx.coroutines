package kotlinx.coroutines.debug.test

import kotlinx.coroutines.debug.manager.*
import org.junit.After
import org.junit.Assert
import org.junit.Before
import org.junit.BeforeClass
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

typealias CoroutineName = String
typealias Dump = String

open class DebuggerTestBase {
    @Before
    fun debuggableTestBefore() {
        DebuggerTestAssertions.beforeTest()
    }

    @After
    fun debuggableTestAfter() {
        DebuggerTestAssertions.onCompletion()
    }

    companion object {
        @JvmStatic
        @BeforeClass
        fun debuggableTestBeforeClass() {
            DebuggerTestUtils.tryBuildDebuggerIndexes()
        }
    }
}

object DebuggerTestUtils {
    fun tryBuildDebuggerIndexes() {
        val classLoader = Thread.currentThread().contextClassLoader
        if (System.getProperty(PROPERTY_ENABLE_DEBUG).toBoolean()) {
            DebuggerTestAssertions.enabled = true
            val logLevel = try {
                System.getProperty(PROPERTY_DEBUG_LOG_LEVEL)?.let { LogLevel.valueOf(it.toUpperCase()) }
            } catch (_: IllegalArgumentException) {
                null
            } ?: LogLevel.INFO
            Logger.config = LoggerConfig(logLevel)
            val suspendCallsIndex = classLoader.getResources(ALL_SUSPEND_CALLS_DUMP_FILE_NAME).toList()
            debug { "suspend calls indexes: ${suspendCallsIndex.toList()}" }
            allSuspendCallsMap.putAll(
                    suspendCallsIndex.flatMap {
                        it.openStream().bufferedReader().readLines().map { it.readKV(SuspendCall) }
                    })
            val doResumeFunctionsIndex = classLoader.getResources(KNOWND_DORESUME_FUNCTIONS_DUMP_FILE_NAME).toList()
            debug { "doResume functions indexes: ${doResumeFunctionsIndex.toList()}" }
            knownDoResumeFunctionsMap.putAll(
                    doResumeFunctionsIndex.flatMap {
                        it.openStream().bufferedReader().readLines().map { it.readKV(MethodId) }
                    })
            debug { "allSuspendCallsMap.size: ${allSuspendCallsMap.size}" }
            debug { "knownDoResumeFunctionsMap.size: ${knownDoResumeFunctionsMap.size}" }
        }
    }
}

object DebuggerTestAssertions {
    var enabled = false
    fun assertDebuggerPausedHereState(vararg expected: Coroutine) {
        if (!enabled) return
        assertMatches(expected.toList(), extractFixedCoroutineDumpsAsInDebugger())
    }

    fun beforeTest() {
        if (!enabled) return
        resetCoroutineId()
        expectedStates.clear()
        StacksManager.reset()
        exceptions = AppendOnlyThreadSafeList()
        StacksManager.addOnStackChangedCallback(onStateChanged)
    }

    fun onCompletion() {
        if (!enabled) return
        Assert.assertTrue("exceptions were thrown: ${exceptions!!.toList()}", exceptions!!.isEmpty())
        exceptions = null
        StacksManager.removeOnStackChangedCallback(onStateChanged)
    }

    fun expectNoCoroutines(customFilter: CoroutineSnapshot.() -> Boolean = { true }) {
        if (!enabled) return
        val coroutines = StacksManager.getSnapshot().coroutines.filter(customFilter)
        Assert.assertTrue("expected nothing, got: $coroutines", coroutines.isEmpty())
    }

    fun expectNoSuspendCoroutines() = expectNoCoroutines({ status == CoroutineStatus.Suspended })

    fun expectNextSuspendedState(vararg coroutines: Coroutine) {
        if (!enabled) return
        expectedStates[nextExpectedIndex.getAndIncrement()] = ExpectedState(coroutines.toList())
    }

    private fun resetCoroutineId() {
        Class.forName("kotlinx.coroutines.experimental.CoroutineContextKt")
                .getDeclaredMethod("resetCoroutineId").invoke(null)
    }

    private var stateIndex = AtomicInteger(0)

    private data class ExpectedState(val coroutines: List<Coroutine>)

    private val NAME_AND_STATUS_FROM_COROUTINE_DUMP =
            "^\\\"(.+)\\\".*\n {2}Status:\\s([A-Za-z]+).*(\n.*)?".toRegex(RegexOption.DOT_MATCHES_ALL)

    private fun extractNameFromCoroutineDump(dump: String): String {
        val (_, name, _) = requireNotNull(NAME_AND_STATUS_FROM_COROUTINE_DUMP.find(dump)?.groupValues,
                { "Can't extract name and status from '$dump'" })
        return name
    }

    private val THIS_CLASS_NAME = this.javaClass.canonicalName

    private fun extractFixedCoroutineDumpsAsInDebugger(): Map<CoroutineName, Dump> {
        val dump = likeInDebugTextStateDump()
        return dump.substring(dump.indexOf('\n') + 1) //drop header
                .split("\n\n").dropLast(1).map {
            var (currentDump, name, status) = requireNotNull(NAME_AND_STATUS_FROM_COROUTINE_DUMP.find(it)?.groupValues,
                    { "Can't parse coroutine dump:\n $dump" })
            if (status.toLowerCase() == "running") {
                val parts = currentDump.split('\n')
                var index = 2 //top stack frame
                while (parts[index].startsWith("    at ${THIS_CLASS_NAME}")) {
                    index++
                }
                currentDump = (parts.take(2) + parts.drop(index)).joinToString("\n")
            }
            name to currentDump
        }.toMap()
    }

    private fun likeInDebugTextStateDump(): String =
            Class.forName("kotlinx.coroutines.debug.manager.StacksManager")
                    .getDeclaredMethod("getFullDumpString").invoke(null) as String

    private fun assertMatches(expected: List<Coroutine>, actual: Map<CoroutineName, Dump>) {
        Assert.assertTrue("expected: ${expected.map { it.name }}, got: ${actual.keys}",
                expected.map { it.name }.toSet() == actual.keys.toSet())
        for (coroutine in expected) {
            val dump = actual[coroutine.name]!!.trim('\n')
            val message = buildString {
                append(coroutine.pattern.joinToString("\n", "expected:\n", "\n") { it.symbol.string })
                append("actual:\n$dump")
            }
            Assert.assertTrue(message, coroutine.matchEntireString(dump))
        }
    }

    private val onStateChanged = { manager: StacksManager, event: StackChangedEvent, _: WrappedContext ->
        if (event == StackChangedEvent.Suspended && expectedStates.isNotEmpty()) {
            val currentState = stateIndex.getAndIncrement()
            val expected = expectedStates[currentState]
            if (expected == null) println("no check for state: $currentState")
            else {
                val actual = manager.getSnapshot().coroutines.filter { it.status == CoroutineStatus.Suspended }
                        .map { it.coroutineInfo(Thread.currentThread(), Configuration.Debug).toString() }
                        .map { extractNameFromCoroutineDump(it) to it }.toMap()
                assertMatches(expected.coroutines, actual)
            }
        }
    }

    private var expectedStates = ConcurrentHashMap<Int, ExpectedState>()
    private val nextExpectedIndex = AtomicInteger(0)
}