/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import org.junit.rules.Timeout.*
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

@RunWith(Parameterized::class)
class BuildersKtTest(
    private val disp1: CoroutineContext,
    private val disp2: CoroutineContext,
    private val disp3: CoroutineContext,
    private val disp4: CoroutineContext
) {
    companion object {
        const val STEP: Long = 100

        private val allParams = listOf(
            EmptyCoroutineContext,
            Executors.newSingleThreadExecutor().asCoroutineDispatcher(),
            Executors.newSingleThreadScheduledExecutor().asCoroutineDispatcher(),
            Dispatchers.Default,
            Dispatchers.IO,
//            Dispatchers.Main,
        )

        @ExperimentalStdlibApi
        @JvmStatic
        @Parameterized.Parameters
        fun data(): List<*> = buildList {
            allParams.forEach { i1 ->
                allParams.forEach { i2 ->
                    allParams.forEach { i3 ->
                        allParams.forEach { i4 ->
                            add(arrayOf(i1, i2, i3, i4))
                        }
                    }
                }
            }
        }
    }

    // Hard deadLock detect
    @Rule
    @JvmField
    var globalTimeout: Timeout = millis(STEP * 5 * 2)

    @Test
    fun testTemplate(): Unit =
        runBlocking(disp1) {
            runCatching {
                // Soft deadLock detect
                withTimeout(STEP * 5) {
                    delay(STEP)
                    withContext(disp2) {
                        delay(STEP)
                    }
                    runBlocking(disp3) {
                        // Soft deadLock detect
                        runCatching {
                            withTimeout(STEP * 3) {
                                delay(STEP)
                                withContext(disp4) {
                                    delay(STEP)
                                }
                            }
                        }.onFailure {
                            when (it) {
                                is TimeoutException, is TimeoutCancellationException -> fail(
                                    "DEADLOCK on Level2",
                                    it
                                )
                                else -> fail("other exception on Level2", it)
                            }
                        }.getOrThrow()
                    }
                }
            }.onFailure {
                when (it) {
                    is TimeoutException, is TimeoutCancellationException -> fail("DEADLOCK on Level1", it)
                    else -> fail("other exception on Level2", it)
                }
            }.getOrThrow()
        }
}