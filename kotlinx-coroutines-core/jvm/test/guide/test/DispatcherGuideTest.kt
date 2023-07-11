/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutine-context-and-dispatchers.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class DispatcherGuideTest {
    @Test
    fun testExampleContext01() {
        test("ExampleContext01") { kotlinx.coroutines.guide.exampleContext01.main() }.verifyLinesStartUnordered(
            "Unconfined            : I'm working in thread main",
            "Default               : I'm working in thread DefaultDispatcher-worker-1",
            "newSingleThreadContext: I'm working in thread MyOwnThread",
            "main runBlocking      : I'm working in thread main"
        )
    }

    @Test
    fun testExampleContext02() {
        test("ExampleContext02") { kotlinx.coroutines.guide.exampleContext02.main() }.verifyLinesStart(
            "Unconfined      : I'm working in thread main",
            "main runBlocking: I'm working in thread main",
            "Unconfined      : After delay in thread kotlinx.coroutines.DefaultExecutor",
            "main runBlocking: After delay in thread main"
        )
    }

    @Test
    fun testExampleContext03() {
        test("ExampleContext03") { kotlinx.coroutines.guide.exampleContext03.main() }.verifyLinesFlexibleThread(
            "[main @coroutine#2] I'm computing a piece of the answer",
            "[main @coroutine#3] I'm computing another piece of the answer",
            "[main @coroutine#1] The answer is 42"
        )
    }

    @Test
    fun testExampleContext04() {
        test("ExampleContext04") { kotlinx.coroutines.guide.exampleContext04.main() }.verifyLines(
            "[Ctx1 @coroutine#1] Started in ctx1",
            "[Ctx2 @coroutine#1] Working in ctx2",
            "[Ctx1 @coroutine#1] Back to ctx1"
        )
    }

    @Test
    fun testExampleContext05() {
        test("ExampleContext05") { kotlinx.coroutines.guide.exampleContext05.main() }.also { lines ->
            check(lines.size == 1 && lines[0].startsWith("My job is \"coroutine#1\":BlockingCoroutine{Active}@"))
        }
    }

    @Test
    fun testExampleContext06() {
        test("ExampleContext06") { kotlinx.coroutines.guide.exampleContext06.main() }.verifyLines(
            "job1: I run in my own Job and execute independently!",
            "job2: I am a child of the request coroutine",
            "main: Who has survived request cancellation?",
            "job1: I am not affected by cancellation of the request"
        )
    }

    @Test
    fun testExampleContext07() {
        test("ExampleContext07") { kotlinx.coroutines.guide.exampleContext07.main() }.verifyLines(
            "request: I'm done and I don't explicitly join my children that are still active",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Coroutine 2 is done",
            "Now processing of the request is complete"
        )
    }

    @Test
    fun testExampleContext08() {
        test("ExampleContext08") { kotlinx.coroutines.guide.exampleContext08.main() }.verifyLinesFlexibleThread(
            "[main @main#1] Started main coroutine",
            "[main @v1coroutine#2] Computing v1",
            "[main @v2coroutine#3] Computing v2",
            "[main @main#1] The answer for v1 / v2 = 42"
        )
    }

    @Test
    fun testExampleContext09() {
        test("ExampleContext09") { kotlinx.coroutines.guide.exampleContext09.main() }.verifyLinesFlexibleThread(
            "I'm working in thread DefaultDispatcher-worker-1 @test#2"
        )
    }

    @Test
    fun testExampleContext10() {
        test("ExampleContext10") { kotlinx.coroutines.guide.exampleContext10.main() }.verifyLines(
            "Launched coroutines",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Destroying activity!"
        )
    }

    @Test
    fun testExampleContext11() {
        test("ExampleContext11") { kotlinx.coroutines.guide.exampleContext11.main() }.verifyLinesFlexibleThread(
            "Pre-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'",
            "Launch start, current thread: Thread[DefaultDispatcher-worker-1 @coroutine#2,5,main], thread local value: 'launch'",
            "After yield, current thread: Thread[DefaultDispatcher-worker-2 @coroutine#2,5,main], thread local value: 'launch'",
            "Post-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'"
        )
    }
}
