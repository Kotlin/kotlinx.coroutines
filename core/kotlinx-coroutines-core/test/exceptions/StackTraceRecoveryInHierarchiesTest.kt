/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("DeferredResultUnused")

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class StackTraceRecoveryInHierarchiesTest : TestBase() {

    @Test
    fun testNestedAsync() = runTest {
        val rootAsync = async(NonCancellable) {
            expect(1)

            // Just a noise for unwrapping
            async {
                expect(2)
                delay(Long.MAX_VALUE)
            }

            // Do not catch, fail on cancellation
            async {
                expect(3)
                async {
                    expect(4)
                    delay(Long.MAX_VALUE)
                }

                async {
                    expect(5)
                    // 1) await(), catch, verify and rethrow
                    try {
                        val nested = async {
                            expect(6)
                            throw RecoverableTestException()
                        }

                        nested.awaitNested()
                    } catch (e: RecoverableTestException) {
                        expect(7)
                        e.verifyException(
                            "await\$suspendImpl",
                            "awaitNested",
                            "\$testNestedAsync\$1\$rootAsync\$1\$2\$2.invokeSuspend"
                        )
                        // Just rethrow it
                        throw e
                    }
                }
            }
        }

        try {
            rootAsync.awaitRootLevel()
        } catch (e: RecoverableTestException) {
            e.verifyException("await\$suspendImpl", "awaitRootLevel")
            finish(8)
        }
    }

    private suspend fun Deferred<*>.awaitRootLevel() {
        await()
        assertTrue(true)
    }

    private suspend fun Deferred<*>.awaitNested() {
        await()
        assertTrue(true)
    }

    private fun RecoverableTestException.verifyException(vararg expectedTraceElements: String) {
        // It is "recovered" only once
        assertEquals(1, depth())
        val stacktrace = stackTrace.map { it.methodName }.toSet()
        assertTrue(expectedTraceElements.all { stacktrace.contains(it) })
    }

    private fun Throwable.depth(): Int {
        val cause = cause ?: return 0
        return 1 + cause.depth()
    }
}
