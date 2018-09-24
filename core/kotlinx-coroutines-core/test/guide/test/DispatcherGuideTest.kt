// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class DispatchersGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext01() {
        test("KotlinxCoroutinesExperimentalGuideContext01") { kotlinx.coroutines.experimental.guide.context01.main(emptyArray()) }.verifyLinesStartUnordered(
            "Unconfined            : I'm working in thread main",
            "Default               : I'm working in thread CommonPool-worker-1",
            "newSingleThreadContext: I'm working in thread MyOwnThread",
            "main runBlocking      : I'm working in thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext02() {
        test("KotlinxCoroutinesExperimentalGuideContext02") { kotlinx.coroutines.experimental.guide.context02.main(emptyArray()) }.verifyLinesStart(
            "Unconfined      : I'm working in thread main",
            "main runBlocking: I'm working in thread main",
            "Unconfined      : After delay in thread kotlinx.coroutines.DefaultExecutor",
            "main runBlocking: After delay in thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext03() {
        test("KotlinxCoroutinesExperimentalGuideContext03") { kotlinx.coroutines.experimental.guide.context03.main(emptyArray()) }.verifyLinesFlexibleThread(
            "[main @coroutine#2] I'm computing a piece of the answer",
            "[main @coroutine#3] I'm computing another piece of the answer",
            "[main @coroutine#1] The answer is 42"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext04() {
        test("KotlinxCoroutinesExperimentalGuideContext04") { kotlinx.coroutines.experimental.guide.context04.main(emptyArray()) }.verifyLines(
            "[Ctx1 @coroutine#1] Started in ctx1",
            "[Ctx2 @coroutine#1] Working in ctx2",
            "[Ctx1 @coroutine#1] Back to ctx1"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext05() {
        test("KotlinxCoroutinesExperimentalGuideContext05") { kotlinx.coroutines.experimental.guide.context05.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0].startsWith("My job is \"coroutine#1\":BlockingCoroutine{Active}@"))
        }
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext06() {
        test("KotlinxCoroutinesExperimentalGuideContext06") { kotlinx.coroutines.experimental.guide.context06.main(emptyArray()) }.verifyLines(
            "job1: I run in GlobalScope and execute independently!",
            "job2: I am a child of the request coroutine",
            "job1: I am not affected by cancellation of the request",
            "main: Who has survived request cancellation?"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext07() {
        test("KotlinxCoroutinesExperimentalGuideContext07") { kotlinx.coroutines.experimental.guide.context07.main(emptyArray()) }.verifyLines(
            "request: I'm done and I don't explicitly join my children that are still active",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Coroutine 2 is done",
            "Now processing of the request is complete"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext08() {
        test("KotlinxCoroutinesExperimentalGuideContext08") { kotlinx.coroutines.experimental.guide.context08.main(emptyArray()) }.verifyLinesFlexibleThread(
            "[main @main#1] Started main coroutine",
            "[main @v1coroutine#2] Computing v1",
            "[main @v2coroutine#3] Computing v2",
            "[main @main#1] The answer for v1 / v2 = 42"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext09() {
        test("KotlinxCoroutinesExperimentalGuideContext09") { kotlinx.coroutines.experimental.guide.context09.main(emptyArray()) }.verifyLinesFlexibleThread(
            "I'm working in thread CommonPool-worker-1 @test#2"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext10() {
        test("KotlinxCoroutinesExperimentalGuideContext10") { kotlinx.coroutines.experimental.guide.context10.main(emptyArray()) }.verifyLines(
            "Launched coroutines",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Destroying activity!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext11() {
        test("KotlinxCoroutinesExperimentalGuideContext11") { kotlinx.coroutines.experimental.guide.context11.main(emptyArray()) }.verifyLinesFlexibleThread(
            "Pre-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'",
            "Launch start, current thread: Thread[CommonPool-worker-1 @coroutine#2,5,main], thread local value: 'launch'",
            "After yield, current thread: Thread[CommonPool-worker-2 @coroutine#2,5,main], thread local value: 'launch'",
            "Post-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'"
        )
    }
}
