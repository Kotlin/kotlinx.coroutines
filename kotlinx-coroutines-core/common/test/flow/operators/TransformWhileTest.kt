/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class TransformWhileTest : TestBase() {
    @Test
    fun testSimple() = runTest {
        val flow = (0..10).asFlow()
        val expected = listOf("A", "B", "C", "D")
        val actual = flow.transformWhile { value ->
            when(value) {
                0 -> { emit("A"); true }
                1 -> true
                2 -> { emit("B"); emit("C"); true }
                3 -> { emit("D"); false }
                else -> { expectUnreached(); false }
            }
        }.toList()
        assertEquals(expected, actual)
    }

    @Test
    fun testCancelUpstream() = runTest {
        var cancelled = false
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    hang { cancelled = true }
                }
                emit(1)
                emit(2)
                emit(3)
            }
        }
        val transformed = flow.transformWhile {
            emit(it)
            it < 2
        }
        assertEquals(listOf(1, 2), transformed.toList())
        assertTrue(cancelled)
    }
    
    @Test
    fun testExample() = runTest {
        val source = listOf(
            DownloadProgress(0),
            DownloadProgress(50),
            DownloadProgress(100),
            DownloadProgress(147)
        )
        val expected = source.subList(0, 3)
        val actual = source.asFlow().completeWhenDone().toList()
        assertEquals(expected, actual)
    }

    private fun Flow<DownloadProgress>.completeWhenDone(): Flow<DownloadProgress> =
        transformWhile { progress ->
            emit(progress) // always emit progress
            !progress.isDone() // continue while download is not done
        }

    private data class DownloadProgress(val percent: Int) {
        fun isDone() = percent >= 100
    }
}