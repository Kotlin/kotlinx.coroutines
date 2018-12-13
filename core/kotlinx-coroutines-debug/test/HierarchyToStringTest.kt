/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class HierarchyToStringTest : TestBase() {

    @Before
    fun setUp() {
        before()
        DebugProbes.sanitizeStackTraces = false
        DebugProbes.install()
    }

    @After
    fun tearDown() {
        try {
            DebugProbes.uninstall()
        } finally {
            onCompletion()
        }
    }

    @Test
    fun testCompletingHierarchy() = runBlocking {
        val tab = '\t'
        val expectedString = """
            "coroutine#2":StandaloneCoroutine{Completing}
            $tab"foo#3":DeferredCoroutine{Active}, continuation is SUSPENDED at line HierarchyToStringTest${'$'}launchHierarchy${'$'}1${'$'}1.invokeSuspend(HierarchyToStringTest.kt:30)
            $tab"coroutine#4":ActorCoroutine{Active}, continuation is SUSPENDED at line HierarchyToStringTest${'$'}launchHierarchy${'$'}1${'$'}2${'$'}1.invokeSuspend(HierarchyToStringTest.kt:40)
            $tab$tab"coroutine#5":StandaloneCoroutine{Active}, continuation is SUSPENDED at line HierarchyToStringTest${'$'}launchHierarchy${'$'}1${'$'}2${'$'}job$1.invokeSuspend(HierarchyToStringTest.kt:37)
            """.trimIndent()

        checkHierarchy(isCompleting = true, expectedString = expectedString)
    }

    @Test
    fun testActiveHierarchy() = runBlocking {
        val tab = '\t'
        val expectedString = """
            "coroutine#2":StandaloneCoroutine{Active}, continuation is SUSPENDED at line HierarchyToStringTest${'$'}launchHierarchy${'$'}1.invokeSuspend(HierarchyToStringTest.kt:94)
            $tab"foo#3":DeferredCoroutine{Active}, continuation is SUSPENDED at line HierarchyToStringTest${'$'}launchHierarchy${'$'}1${'$'}1.invokeSuspend(HierarchyToStringTest.kt:30)
            $tab"coroutine#4":ActorCoroutine{Active}, continuation is SUSPENDED at line HierarchyToStringTest${'$'}launchHierarchy${'$'}1${'$'}2${'$'}1.invokeSuspend(HierarchyToStringTest.kt:40)
            $tab$tab"coroutine#5":StandaloneCoroutine{Active}, continuation is SUSPENDED at line HierarchyToStringTest${'$'}launchHierarchy${'$'}1${'$'}2${'$'}job$1.invokeSuspend(HierarchyToStringTest.kt:37)
            """.trimIndent()
        checkHierarchy(isCompleting = false, expectedString = expectedString)
    }

    private suspend fun CoroutineScope.checkHierarchy(isCompleting: Boolean, expectedString: String) {
        val root = launchHierarchy(isCompleting)
        repeat(4) { yield() }
        expect(6)
        assertEquals(
            expectedString.trimStackTrace().trimPackage(),
            DebugProbes.hierarchyToString(root).trimEnd().trimStackTrace().trimPackage()
        )
        root.cancel()
        root.join()
        finish(7)
    }

    private fun CoroutineScope.launchHierarchy(isCompleting: Boolean): Job {
        return launch {
            expect(1)
            async(CoroutineName("foo")) {
                expect(2)
                delay(Long.MAX_VALUE)
            }

            actor<Int> {
                expect(3)
                val job = launch {
                    expect(4)
                    delay(Long.MAX_VALUE)
                }

                withContext(wrapperDispatcher(coroutineContext)) {
                    expect(5)
                    job.join()
                }
            }

            if (!isCompleting) {
                delay(Long.MAX_VALUE)
            }
        }
    }

    private fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
        val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
        return object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                dispatcher.dispatch(context, block)
            }
        }
    }
}
