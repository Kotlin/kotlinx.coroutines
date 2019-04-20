// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class DispatchersGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideContext01() {
        test("KotlinxCoroutinesGuideContext01") { kotlinx.coroutines.guide.context01.main() }.verifyLinesStartUnordered(
            "Unconfined            : I'm working in thread main",
            "Default               : I'm working in thread DefaultDispatcher-worker-1",
            "newSingleThreadContext: I'm working in thread MyOwnThread",
            "main runBlocking      : I'm working in thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext02() {
        test("KotlinxCoroutinesGuideContext02") { kotlinx.coroutines.guide.context02.main() }.verifyLinesStart(
            "Unconfined      : I'm working in thread main",
            "main runBlocking: I'm working in thread main",
            "Unconfined      : After delay in thread kotlinx.coroutines.DefaultExecutor",
            "main runBlocking: After delay in thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext03() {
        test("KotlinxCoroutinesGuideContext03") { kotlinx.coroutines.guide.context03.main() }.verifyLinesFlexibleThread(
            "[main @coroutine#2] I'm computing a piece of the answer",
            "[main @coroutine#3] I'm computing another piece of the answer",
            "[main @coroutine#1] The answer is 42"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext04() {
        test("KotlinxCoroutinesGuideContext04") { kotlinx.coroutines.guide.context04.main() }.verifyLines(
            "[Ctx1 @coroutine#1] Started in ctx1",
            "[Ctx2 @coroutine#1] Working in ctx2",
            "[Ctx1 @coroutine#1] Back to ctx1"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext05() {
        test("KotlinxCoroutinesGuideContext05") { kotlinx.coroutines.guide.context05.main() }.also { lines ->
            check(lines.size == 1 && lines[0].startsWith("My job is \"coroutine#1\":BlockingCoroutine{Active}@"))
        }
    }

    @Test
    fun testKotlinxCoroutinesGuideContext06() {
        test("KotlinxCoroutinesGuideContext06") { kotlinx.coroutines.guide.context06.main() }.verifyLines(
            "job1: I run in GlobalScope and execute independently!",
            "job2: I am a child of the request coroutine",
            "job1: I am not affected by cancellation of the request",
            "main: Who has survived request cancellation?"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext07() {
        test("KotlinxCoroutinesGuideContext07") { kotlinx.coroutines.guide.context07.main() }.verifyLines(
            "request: I'm done and I don't explicitly join my children that are still active",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Coroutine 2 is done",
            "Now processing of the request is complete"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext08() {
        test("KotlinxCoroutinesGuideContext08") { kotlinx.coroutines.guide.context08.main() }.verifyLinesFlexibleThread(
            "[main @main#1] Started main coroutine",
            "[main @v1coroutine#2] Computing v1",
            "[main @v2coroutine#3] Computing v2",
            "[main @main#1] The answer for v1 / v2 = 42"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext09() {
        test("KotlinxCoroutinesGuideContext09") { kotlinx.coroutines.guide.context09.main() }.verifyLinesFlexibleThread(
            "I'm working in thread DefaultDispatcher-worker-1 @test#2"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext10() {
        test("KotlinxCoroutinesGuideContext10") { kotlinx.coroutines.guide.context10.main() }.verifyLines(
            "Launched coroutines",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Destroying activity!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext11() {
        test("KotlinxCoroutinesGuideContext11") { kotlinx.coroutines.guide.context11.main() }.verifyLinesFlexibleThread(
            "Pre-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'",
            "Launch start, current thread: Thread[DefaultDispatcher-worker-1 @coroutine#2,5,main], thread local value: 'launch'",
            "After yield, current thread: Thread[DefaultDispatcher-worker-2 @coroutine#2,5,main], thread local value: 'launch'",
            "Post-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'"
        )
    }
}
