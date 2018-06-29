// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class GuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic01() {
        test("KotlinxCoroutinesExperimentalGuideBasic01") { kotlinx.coroutines.experimental.guide.basic01.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic02() {
        test("KotlinxCoroutinesExperimentalGuideBasic02") { kotlinx.coroutines.experimental.guide.basic02.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic02b() {
        test("KotlinxCoroutinesExperimentalGuideBasic02b") { kotlinx.coroutines.experimental.guide.basic02b.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic03() {
        test("KotlinxCoroutinesExperimentalGuideBasic03") { kotlinx.coroutines.experimental.guide.basic03.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic04() {
        test("KotlinxCoroutinesExperimentalGuideBasic04") { kotlinx.coroutines.experimental.guide.basic04.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic05() {
        test("KotlinxCoroutinesExperimentalGuideBasic05") { kotlinx.coroutines.experimental.guide.basic05.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0] == ".".repeat(100_000))
        }
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic06() {
        test("KotlinxCoroutinesExperimentalGuideBasic06") { kotlinx.coroutines.experimental.guide.basic06.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ..."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel01() {
        test("KotlinxCoroutinesExperimentalGuideCancel01") { kotlinx.coroutines.experimental.guide.cancel01.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel02() {
        test("KotlinxCoroutinesExperimentalGuideCancel02") { kotlinx.coroutines.experimental.guide.cancel02.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm sleeping 3 ...",
            "I'm sleeping 4 ...",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel03() {
        test("KotlinxCoroutinesExperimentalGuideCancel03") { kotlinx.coroutines.experimental.guide.cancel03.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel04() {
        test("KotlinxCoroutinesExperimentalGuideCancel04") { kotlinx.coroutines.experimental.guide.cancel04.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm running finally",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel05() {
        test("KotlinxCoroutinesExperimentalGuideCancel05") { kotlinx.coroutines.experimental.guide.cancel05.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm running finally",
            "And I've just delayed for 1 sec because I'm non-cancellable",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel06() {
        test("KotlinxCoroutinesExperimentalGuideCancel06") { kotlinx.coroutines.experimental.guide.cancel06.main(emptyArray()) }.verifyLinesStartWith(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Exception in thread \"main\" kotlinx.coroutines.experimental.TimeoutCancellationException: Timed out waiting for 1300 MILLISECONDS"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel07() {
        test("KotlinxCoroutinesExperimentalGuideCancel07") { kotlinx.coroutines.experimental.guide.cancel07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Result is null"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose01() {
        test("KotlinxCoroutinesExperimentalGuideCompose01") { kotlinx.coroutines.experimental.guide.compose01.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 2017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose02() {
        test("KotlinxCoroutinesExperimentalGuideCompose02") { kotlinx.coroutines.experimental.guide.compose02.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose03() {
        test("KotlinxCoroutinesExperimentalGuideCompose03") { kotlinx.coroutines.experimental.guide.compose03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 2017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose04() {
        test("KotlinxCoroutinesExperimentalGuideCompose04") { kotlinx.coroutines.experimental.guide.compose04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1085 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext01() {
        test("KotlinxCoroutinesExperimentalGuideContext01") { kotlinx.coroutines.experimental.guide.context01.main(emptyArray()) }.verifyLinesStartUnordered(
            "      'Unconfined': I'm working in thread main",
            "      'CommonPool': I'm working in thread ForkJoinPool.commonPool-worker-1",
            "          'newSTC': I'm working in thread MyOwnThread",
            "'coroutineContext': I'm working in thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext02() {
        test("KotlinxCoroutinesExperimentalGuideContext02") { kotlinx.coroutines.experimental.guide.context02.main(emptyArray()) }.verifyLinesStart(
            "      'Unconfined': I'm working in thread main",
            "'coroutineContext': I'm working in thread main",
            "      'Unconfined': After delay in thread kotlinx.coroutines.DefaultExecutor",
            "'coroutineContext': After delay in thread main"
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
            "job1: I have my own context and execute independently!",
            "job2: I am a child of the request coroutine",
            "job1: I am not affected by cancellation of the request",
            "main: Who has survived request cancellation?"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext07() {
        test("KotlinxCoroutinesExperimentalGuideContext07") { kotlinx.coroutines.experimental.guide.context07.main(emptyArray()) }.verifyLines(
            "job: I am a child of the request coroutine, but with a different dispatcher",
            "main: Who has survived request cancellation?"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext08() {
        test("KotlinxCoroutinesExperimentalGuideContext08") { kotlinx.coroutines.experimental.guide.context08.main(emptyArray()) }.verifyLines(
            "request: I'm done and I don't explicitly join my children that are still active",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Coroutine 2 is done",
            "Now processing of the request is complete"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext09() {
        test("KotlinxCoroutinesExperimentalGuideContext09") { kotlinx.coroutines.experimental.guide.context09.main(emptyArray()) }.verifyLinesFlexibleThread(
            "[main @main#1] Started main coroutine",
            "[ForkJoinPool.commonPool-worker-1 @v1coroutine#2] Computing v1",
            "[ForkJoinPool.commonPool-worker-2 @v2coroutine#3] Computing v2",
            "[main @main#1] The answer for v1 / v2 = 42"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideContext10() {
        test("KotlinxCoroutinesExperimentalGuideContext10") { kotlinx.coroutines.experimental.guide.context10.main(emptyArray()) }.verifyLines(
            "Launched 10 coroutines",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Cancelling the job!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel01() {
        test("KotlinxCoroutinesExperimentalGuideChannel01") { kotlinx.coroutines.experimental.guide.channel01.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel02() {
        test("KotlinxCoroutinesExperimentalGuideChannel02") { kotlinx.coroutines.experimental.guide.channel02.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel03() {
        test("KotlinxCoroutinesExperimentalGuideChannel03") { kotlinx.coroutines.experimental.guide.channel03.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel04() {
        test("KotlinxCoroutinesExperimentalGuideChannel04") { kotlinx.coroutines.experimental.guide.channel04.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel05() {
        test("KotlinxCoroutinesExperimentalGuideChannel05") { kotlinx.coroutines.experimental.guide.channel05.main(emptyArray()) }.verifyLines(
            "2",
            "3",
            "5",
            "7",
            "11",
            "13",
            "17",
            "19",
            "23",
            "29"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel06() {
        test("KotlinxCoroutinesExperimentalGuideChannel06") { kotlinx.coroutines.experimental.guide.channel06.main(emptyArray()) }.also { lines ->
            check(lines.size == 10 && lines.withIndex().all { (i, line) -> line.startsWith("Processor #") && line.endsWith(" received ${i + 1}") })
        }
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel07() {
        test("KotlinxCoroutinesExperimentalGuideChannel07") { kotlinx.coroutines.experimental.guide.channel07.main(emptyArray()) }.verifyLines(
            "foo",
            "foo",
            "BAR!",
            "foo",
            "foo",
            "BAR!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel08() {
        test("KotlinxCoroutinesExperimentalGuideChannel08") { kotlinx.coroutines.experimental.guide.channel08.main(emptyArray()) }.verifyLines(
            "Sending 0",
            "Sending 1",
            "Sending 2",
            "Sending 3",
            "Sending 4"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel10() {
        test("KotlinxCoroutinesExperimentalGuideChannel10") { kotlinx.coroutines.experimental.guide.channel10.main(emptyArray()) }.verifyLines(
            "Initial element is available immediately: kotlin.Unit",
            "Next element is not ready in 50 ms: null",
            "Next element is ready in 100 ms: kotlin.Unit",
            "Consumer pauses for 150ms",
            "Next element is available immediately after large consumer delay: kotlin.Unit",
            "Next element is ready in 50ms after consumer pause in 150ms: kotlin.Unit"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel09() {
        test("KotlinxCoroutinesExperimentalGuideChannel09") { kotlinx.coroutines.experimental.guide.channel09.main(emptyArray()) }.verifyLines(
            "ping Ball(hits=1)",
            "pong Ball(hits=2)",
            "ping Ball(hits=3)",
            "pong Ball(hits=4)"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync01() {
        test("KotlinxCoroutinesExperimentalGuideSync01") { kotlinx.coroutines.experimental.guide.sync01.main(emptyArray()) }.verifyLinesStart(
            "Completed 1000000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync01b() {
        test("KotlinxCoroutinesExperimentalGuideSync01b") { kotlinx.coroutines.experimental.guide.sync01b.main(emptyArray()) }.verifyLinesStart(
            "Completed 1000000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync02() {
        test("KotlinxCoroutinesExperimentalGuideSync02") { kotlinx.coroutines.experimental.guide.sync02.main(emptyArray()) }.verifyLinesStart(
            "Completed 1000000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync03() {
        test("KotlinxCoroutinesExperimentalGuideSync03") { kotlinx.coroutines.experimental.guide.sync03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync04() {
        test("KotlinxCoroutinesExperimentalGuideSync04") { kotlinx.coroutines.experimental.guide.sync04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync05() {
        test("KotlinxCoroutinesExperimentalGuideSync05") { kotlinx.coroutines.experimental.guide.sync05.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync06() {
        test("KotlinxCoroutinesExperimentalGuideSync06") { kotlinx.coroutines.experimental.guide.sync06.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync07() {
        test("KotlinxCoroutinesExperimentalGuideSync07") { kotlinx.coroutines.experimental.guide.sync07.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect01() {
        test("KotlinxCoroutinesExperimentalGuideSelect01") { kotlinx.coroutines.experimental.guide.select01.main(emptyArray()) }.verifyLines(
            "fizz -> 'Fizz'",
            "buzz -> 'Buzz!'",
            "fizz -> 'Fizz'",
            "fizz -> 'Fizz'",
            "buzz -> 'Buzz!'",
            "fizz -> 'Fizz'",
            "buzz -> 'Buzz!'"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect02() {
        test("KotlinxCoroutinesExperimentalGuideSelect02") { kotlinx.coroutines.experimental.guide.select02.main(emptyArray()) }.verifyLines(
            "a -> 'Hello 0'",
            "a -> 'Hello 1'",
            "b -> 'World 0'",
            "a -> 'Hello 2'",
            "a -> 'Hello 3'",
            "b -> 'World 1'",
            "Channel 'a' is closed",
            "Channel 'a' is closed"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect03() {
        test("KotlinxCoroutinesExperimentalGuideSelect03") { kotlinx.coroutines.experimental.guide.select03.main(emptyArray()) }.verifyLines(
            "Consuming 1",
            "Side channel has 2",
            "Side channel has 3",
            "Consuming 4",
            "Side channel has 5",
            "Side channel has 6",
            "Consuming 7",
            "Side channel has 8",
            "Side channel has 9",
            "Consuming 10",
            "Done consuming"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect04() {
        test("KotlinxCoroutinesExperimentalGuideSelect04") { kotlinx.coroutines.experimental.guide.select04.main(emptyArray()) }.verifyLines(
            "Deferred 4 produced answer 'Waited for 128 ms'",
            "11 coroutines are still active"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect05() {
        test("KotlinxCoroutinesExperimentalGuideSelect05") { kotlinx.coroutines.experimental.guide.select05.main(emptyArray()) }.verifyLines(
            "BEGIN",
            "Replace",
            "END",
            "Channel was closed"
        )
    }
}
