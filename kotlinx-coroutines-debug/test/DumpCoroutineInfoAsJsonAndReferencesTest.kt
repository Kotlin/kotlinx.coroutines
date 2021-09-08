/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
package kotlinx.coroutines.debug

import com.google.gson.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

@ExperimentalStdlibApi
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
    fun testDumpWithNoCoroutines() {
        val dumpResult = DebugProbesImpl.dumpCoroutinesInfoAsJsonAndReferences()
        assertEquals(dumpResult.size, 4)
        assertIsEmptyArray(dumpResult[1])
        assertIsEmptyArray(dumpResult[2])
        assertIsEmptyArray(dumpResult[3])
    }

    private fun assertIsEmptyArray(obj: Any) =
        assertTrue(obj is Array<*> && obj.isEmpty())

    private fun runTestWithNamedDeferred(name: String?) = runTest {
        val context = if (name == null) EmptyCoroutineContext else CoroutineName(name)
        val deferred = async(context) {
            suspendingMethod()
            assertTrue(true)
        }
        yield()
        verifyDump()
        deferred.cancelAndJoin()
    }

    private suspend fun suspendingMethod() {
        delay(Long.MAX_VALUE)
    }

    private fun verifyDump() {
        val dumpResult = DebugProbesImpl.dumpCoroutinesInfoAsJsonAndReferences()

        assertEquals(dumpResult.size, 4)

        val coroutinesInfoAsJsonString = dumpResult[0]
        val lastObservedThreads = dumpResult[1]
        val lastObservedFrames = dumpResult[2]
        val coroutinesInfo = dumpResult[3]

        assertTrue(coroutinesInfoAsJsonString is String)
        assertTrue(lastObservedThreads is Array<*>)
        assertTrue(lastObservedFrames is Array<*>)
        assertTrue(coroutinesInfo is Array<*>)

        val coroutinesInfoFromJson = Gson().fromJson(coroutinesInfoAsJsonString, Array<CoroutineInfoFromJson>::class.java)

        val size = coroutinesInfo.size
        assertTrue(size != 0)
        assertEquals(size, coroutinesInfoFromJson.size)
        assertEquals(size, lastObservedFrames.size)
        assertEquals(size, lastObservedThreads.size)

        for (i in 0 until size) {
            val info = coroutinesInfo[i]
            val infoFromJson = coroutinesInfoFromJson[i]
            assertTrue(info is DebugCoroutineInfo)
            assertEquals(info.lastObservedThread, lastObservedThreads[i])
            assertEquals(info.lastObservedFrame, lastObservedFrames[i])
            assertEquals(info.sequenceNumber, infoFromJson.sequenceNumber)
            assertEquals(info.state, infoFromJson.state)
            val context = info.context
            assertEquals(context[CoroutineName.Key]?.name, infoFromJson.name)
            assertEquals(context[CoroutineId.Key]?.id, infoFromJson.id)
            assertEquals(context[CoroutineDispatcher.Key]?.toString(), infoFromJson.dispatcher)
        }
    }
}
