/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
package kotlinx.coroutines.debug

import com.google.gson.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import org.junit.Test
import kotlin.test.*

class EnhanceStackTraceWithTreadDumpAsJsonTest : DebugTestBase() {
    private data class StackTraceElementInfoFromJson(
        val declaringClass: String,
        val methodName: String,
        val fileName: String?,
        val lineNumber: Int
    )

    @Test
    fun testEnhancedStackTraceFormatWithDeferred() = runTest {
        val deferred = async {
            suspendingMethod()
            assertTrue(true)
        }
        yield()

        val coroutineInfo = DebugProbesImpl.dumpCoroutinesInfo()
        assertEquals(coroutineInfo.size, 2)
        val info = coroutineInfo[1]
        val enhancedStackTraceAsJsonString = DebugProbesImpl.enhanceStackTraceWithThreadDumpAsJson(info)
        val enhancedStackTraceFromJson = Gson().fromJson(enhancedStackTraceAsJsonString, Array<StackTraceElementInfoFromJson>::class.java)
        val enhancedStackTrace = DebugProbesImpl.enhanceStackTraceWithThreadDump(info, info.lastObservedStackTrace)
        assertEquals(enhancedStackTrace.size, enhancedStackTraceFromJson.size)
        for ((frame, frameFromJson) in enhancedStackTrace.zip(enhancedStackTraceFromJson)) {
            assertEquals(frame.className, frameFromJson.declaringClass)
            assertEquals(frame.methodName, frameFromJson.methodName)
            assertEquals(frame.fileName, frameFromJson.fileName)
            assertEquals(frame.lineNumber, frameFromJson.lineNumber)
        }

        deferred.cancelAndJoin()
    }

    private suspend fun suspendingMethod() {
        delay(Long.MAX_VALUE)
    }
}
