/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import org.junit.*
import kotlin.coroutines.*

class ScopedBuildersTest : DebugTestBase() {

    @Test
    fun testNestedScopes() = runBlocking {
        val job = launch { doInScope() }
        yield()
        yield()
        verifyDump(
            "Coroutine \"coroutine#1\":BlockingCoroutine{Active}@16612a51, state: RUNNING\n" +
             "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)\n",

            "Coroutine \"coroutine#2\":StandaloneCoroutine{Active}@6b53e23f, state: SUSPENDED\n" +
                "\tat kotlinx.coroutines.debug.ScopedBuildersTest\$doWithContext\$2.invokeSuspend(ScopedBuildersTest.kt:49)\n" +
                "\tat kotlinx.coroutines.debug.ScopedBuildersTest.doWithContext(ScopedBuildersTest.kt:47)\n" +
                "\tat kotlinx.coroutines.debug.ScopedBuildersTest\$doInScope\$2.invokeSuspend(ScopedBuildersTest.kt:41)\n" +
                "\tat kotlinx.coroutines.debug.ScopedBuildersTest\$testNestedScopes\$1\$job\$1.invokeSuspend(ScopedBuildersTest.kt:30)\n" +
            "\tat _COROUTINE._CREATION._(CoroutineDebugging.kt)\n" +
                "\tat kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)")
        job.cancelAndJoin()
        finish(4)
    }

    private suspend fun doInScope() = coroutineScope {
        expect(1)
        doWithContext()
        expectUnreached()
    }

    private suspend fun doWithContext() {
        expect(2)
        withContext(wrapperDispatcher(coroutineContext)) {
            expect(3)
            delay(Long.MAX_VALUE)
        }
        expectUnreached()
    }
}
