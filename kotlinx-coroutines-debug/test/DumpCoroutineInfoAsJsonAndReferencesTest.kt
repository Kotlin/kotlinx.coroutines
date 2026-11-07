@file:Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
package kotlinx.coroutines.debug

import com.google.gson.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class DumpCoroutineInfoAsJsonAndReferencesTest : DebugTestBase() {
    private data class CoroutineInfoFromJson(
        val name: String?,
        val id: Long?,
        val dispatcher: String?,
        val sequenceNumber: Long?,
        val state: String?
    )

    @Test
    fun testDumpOfUnnamedCoroutine() =
        runTestWithNamedDeferred(name = null)

    @Test
    fun testDumpOfNamedCoroutine() =
        runTestWithNamedDeferred("Name")

    @Test
    fun testDumpOfNamedCoroutineWithSpecialCharacters() =
        runTestWithNamedDeferred(
            "Name with\n \"special\" characters\\/\t\b",
            "\"Name with\\n \\\"special\\\" characters\\\\/\\t\\b\""
        )

    @Test
    fun testDumpOfNamedCoroutineWithControlCharacters() {
        val expectedByControl = listOf(
            '\u0000' to "\\u0000",
            '\u0001' to "\\u0001",
            '\u0002' to "\\u0002",
            '\u0003' to "\\u0003",
            '\u0004' to "\\u0004",
            '\u0005' to "\\u0005",
            '\u0006' to "\\u0006",
            '\u0007' to "\\u0007",
            '\b' to "\\b",
            '\t' to "\\t",
            '\n' to "\\n",
            '\u000B' to "\\u000b",
            '\u000C' to "\\u000c",
            '\r' to "\\r",
            '\u000E' to "\\u000e",
            '\u000F' to "\\u000f",
            '\u0010' to "\\u0010",
            '\u0011' to "\\u0011",
            '\u0012' to "\\u0012",
            '\u0013' to "\\u0013",
            '\u0014' to "\\u0014",
            '\u0015' to "\\u0015",
            '\u0016' to "\\u0016",
            '\u0017' to "\\u0017",
            '\u0018' to "\\u0018",
            '\u0019' to "\\u0019",
            '\u001A' to "\\u001a",
            '\u001B' to "\\u001b",
            '\u001C' to "\\u001c",
            '\u001D' to "\\u001d",
            '\u001E' to "\\u001e",
            '\u001F' to "\\u001f",
        )
        assertEquals((0..0x1F).map { it.toChar() }, expectedByControl.map { it.first })
        val controls = expectedByControl.joinToString(separator = "") { it.first.toString() }
        val expectedEscapes = expectedByControl.joinToString(separator = "") { it.second }
        val literalBackslashU = "\\" + "u000b"
        val name = "plain \u00E9\uD83D\uDE00\"\\$literalBackslashU $controls tail"
        val expectedEncodedName = buildString {
            append('"')
            append("plain ")
            append('\u00E9')
            append("\uD83D\uDE00")
            append("\\\"")
            append("\\\\")
            append("\\\\u000b")
            append(' ')
            append(expectedEscapes)
            append(" tail")
            append('"')
        }
        runTestWithNamedDeferred(name, expectedEncodedName)
        runTestWithNamedDeferred("", "\"\"")
    }

    @Test
    fun testDumpWithNoCoroutines() {
        val dumpResult = DebugProbesImpl.dumpCoroutinesInfoAsJsonAndReferences()
        assertEquals(dumpResult.size, 4)
        assertIsEmptyArray(dumpResult[1])
        assertIsEmptyArray(dumpResult[2])
        assertIsEmptyArray(dumpResult[3])
    }

    private fun assertIsEmptyArray(obj: Any) =
        assertTrue(obj is Array<*> && obj.isEmpty())

    private fun runTestWithNamedDeferred(name: String?, expectedEncodedName: String? = null) = runTest {
        val context = if (name == null) EmptyCoroutineContext else CoroutineName(name)
        val deferred = async(context) {
            suspendingMethod()
            assertTrue(true)
        }
        yield()
        verifyDump(expectedEncodedName)
        deferred.cancelAndJoin()
    }

    private suspend fun suspendingMethod() {
        delay(Long.MAX_VALUE)
    }

    private fun verifyDump(expectedEncodedName: String? = null) {
        val dumpResult = DebugProbesImpl.dumpCoroutinesInfoAsJsonAndReferences()

        assertEquals(dumpResult.size, 4)

        val coroutinesInfoAsJsonString = dumpResult[0]
        val lastObservedThreads = dumpResult[1]
        val lastObservedFrames = dumpResult[2]
        val coroutinesInfo = dumpResult[3]

        assertIs<String>(coroutinesInfoAsJsonString)
        assertIs<Array<*>>(lastObservedThreads)
        assertIs<Array<*>>(lastObservedFrames)
        assertIs<Array<*>>(coroutinesInfo)
        if (expectedEncodedName != null) {
            val nameLines = coroutinesInfoAsJsonString.lines()
                .map { it.trim() }
                .filter { it.startsWith("\"name\": \"") }
            assertEquals(listOf("\"name\": $expectedEncodedName,"), nameLines)
        }

        val coroutinesInfoFromJson =
            Gson().fromJson(coroutinesInfoAsJsonString, Array<CoroutineInfoFromJson>::class.java)

        val size = coroutinesInfo.size
        assertTrue(size != 0)
        assertEquals(size, coroutinesInfoFromJson.size)
        assertEquals(size, lastObservedFrames.size)
        assertEquals(size, lastObservedThreads.size)

        for (i in 0 until size) {
            val info = coroutinesInfo[i]
            val infoFromJson = coroutinesInfoFromJson[i]
            assertIs<DebugCoroutineInfo>(info)
            assertEquals(info.lastObservedThread, lastObservedThreads[i])
            assertEquals(info.lastObservedFrame, lastObservedFrames[i])
            assertEquals(info.sequenceNumber, infoFromJson.sequenceNumber)
            assertEquals(info.state, infoFromJson.state)
            val context = info.context
            assertEquals(context[CoroutineName.Key]?.name, infoFromJson.name)
            assertEquals(context[CoroutineId.Key]?.id, infoFromJson.id)
            assertEquals(context[ContinuationInterceptor.Key]?.toString(), infoFromJson.dispatcher)
        }
    }
}
