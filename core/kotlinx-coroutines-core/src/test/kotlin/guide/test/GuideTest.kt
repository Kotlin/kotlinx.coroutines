// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.test

import org.junit.Test

class GuideTest {

    @Test
    fun testGuideBasicExample01() {
        test("GuideBasicExample01") { guide.basic.example01.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testGuideBasicExample02() {
        test("GuideBasicExample02") { guide.basic.example02.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testGuideBasicExample03() {
        test("GuideBasicExample03") { guide.basic.example03.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testGuideBasicExample04() {
        test("GuideBasicExample04") { guide.basic.example04.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testGuideBasicExample05() {
        test("GuideBasicExample05") { guide.basic.example05.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0] == ".".repeat(100_000))
        }
    }

    @Test
    fun testGuideBasicExample06() {
        test("GuideBasicExample06") { guide.basic.example06.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ..."
        )
    }

    @Test
    fun testGuideCancelExample01() {
        test("GuideCancelExample01") { guide.cancel.example01.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testGuideCancelExample02() {
        test("GuideCancelExample02") { guide.cancel.example02.main(emptyArray()) }.verifyLines(
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
    fun testGuideCancelExample03() {
        test("GuideCancelExample03") { guide.cancel.example03.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testGuideCancelExample04() {
        test("GuideCancelExample04") { guide.cancel.example04.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm running finally",
            "main: Now I can quit."
        )
    }

    @Test
    fun testGuideCancelExample05() {
        test("GuideCancelExample05") { guide.cancel.example05.main(emptyArray()) }.verifyLines(
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
    fun testGuideCancelExample06() {
        test("GuideCancelExample06") { guide.cancel.example06.main(emptyArray()) }.verifyLinesStartWith(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Exception in thread \"main\" kotlinx.coroutines.experimental.TimeoutCancellationException: Timed out waiting for 1300 MILLISECONDS"
        )
    }

    @Test
    fun testGuideCancelExample07() {
        test("GuideCancelExample07") { guide.cancel.example07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Result is null"
        )
    }

    @Test
    fun testGuideComposeExample01() {
        test("GuideComposeExample01") { guide.compose.example01.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 2017 ms"
        )
    }

    @Test
    fun testGuideComposeExample02() {
        test("GuideComposeExample02") { guide.compose.example02.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testGuideComposeExample03() {
        test("GuideComposeExample03") { guide.compose.example03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 2017 ms"
        )
    }

    @Test
    fun testGuideComposeExample04() {
        test("GuideComposeExample04") { guide.compose.example04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1085 ms"
        )
    }

    @Test
    fun testGuideContextExample01() {
        test("GuideContextExample01") { guide.context.example01.main(emptyArray()) }.verifyLinesStartUnordered(
            "      'Unconfined': I'm working in thread main",
            "      'CommonPool': I'm working in thread ForkJoinPool.commonPool-worker-1",
            "          'newSTC': I'm working in thread MyOwnThread",
            "'coroutineContext': I'm working in thread main"
        )
    }

    @Test
    fun testGuideContextExample02() {
        test("GuideContextExample02") { guide.context.example02.main(emptyArray()) }.verifyLinesStart(
            "      'Unconfined': I'm working in thread main",
            "'coroutineContext': I'm working in thread main",
            "      'Unconfined': After delay in thread kotlinx.coroutines.DefaultExecutor",
            "'coroutineContext': After delay in thread main"
        )
    }

    @Test
    fun testGuideContextExample03() {
        test("GuideContextExample03") { guide.context.example03.main(emptyArray()) }.verifyLinesFlexibleThread(
            "[main @coroutine#2] I'm computing a piece of the answer",
            "[main @coroutine#3] I'm computing another piece of the answer",
            "[main @coroutine#1] The answer is 42"
        )
    }

    @Test
    fun testGuideContextExample04() {
        test("GuideContextExample04") { guide.context.example04.main(emptyArray()) }.verifyLines(
            "[Ctx1 @coroutine#1] Started in ctx1",
            "[Ctx2 @coroutine#1] Working in ctx2",
            "[Ctx1 @coroutine#1] Back to ctx1"
        )
    }

    @Test
    fun testGuideContextExample05() {
        test("GuideContextExample05") { guide.context.example05.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0].startsWith("My job is \"coroutine#1\":BlockingCoroutine{Active}@"))
        }
    }

    @Test
    fun testGuideContextExample06() {
        test("GuideContextExample06") { guide.context.example06.main(emptyArray()) }.verifyLines(
            "job1: I have my own context and execute independently!",
            "job2: I am a child of the request coroutine",
            "job1: I am not affected by cancellation of the request",
            "main: Who has survived request cancellation?"
        )
    }

    @Test
    fun testGuideContextExample07() {
        test("GuideContextExample07") { guide.context.example07.main(emptyArray()) }.verifyLines(
            "job: I am a child of the request coroutine, but with a different dispatcher",
            "main: Who has survived request cancellation?"
        )
    }

    @Test
    fun testGuideContextExample08() {
        test("GuideContextExample08") { guide.context.example08.main(emptyArray()) }.verifyLines(
            "request: I'm done and I don't explicitly join my children that are still active",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Coroutine 2 is done",
            "Now processing of the request is complete"
        )
    }

    @Test
    fun testGuideContextExample09() {
        test("GuideContextExample09") { guide.context.example09.main(emptyArray()) }.verifyLinesFlexibleThread(
            "[main @main#1] Started main coroutine",
            "[ForkJoinPool.commonPool-worker-1 @v1coroutine#2] Computing v1",
            "[ForkJoinPool.commonPool-worker-2 @v2coroutine#3] Computing v2",
            "[main @main#1] The answer for v1 / v2 = 42"
        )
    }

    @Test
    fun testGuideContextExample10() {
        test("GuideContextExample10") { guide.context.example10.main(emptyArray()) }.verifyLines(
            "Launched 10 coroutines",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Cancelling the job!"
        )
    }

    @Test
    fun testGuideChannelExample01() {
        test("GuideChannelExample01") { guide.channel.example01.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testGuideChannelExample02() {
        test("GuideChannelExample02") { guide.channel.example02.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testGuideChannelExample03() {
        test("GuideChannelExample03") { guide.channel.example03.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testGuideChannelExample04() {
        test("GuideChannelExample04") { guide.channel.example04.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testGuideChannelExample05() {
        test("GuideChannelExample05") { guide.channel.example05.main(emptyArray()) }.verifyLines(
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
    fun testGuideChannelExample06() {
        test("GuideChannelExample06") { guide.channel.example06.main(emptyArray()) }.also { lines ->
            check(lines.size == 10 && lines.withIndex().all { (i, line) -> line.startsWith("Processor #") && line.endsWith(" received ${i + 1}") })
        }
    }

    @Test
    fun testGuideChannelExample07() {
        test("GuideChannelExample07") { guide.channel.example07.main(emptyArray()) }.verifyLines(
            "foo",
            "foo",
            "BAR!",
            "foo",
            "foo",
            "BAR!"
        )
    }

    @Test
    fun testGuideChannelExample08() {
        test("GuideChannelExample08") { guide.channel.example08.main(emptyArray()) }.verifyLines(
            "Sending 0",
            "Sending 1",
            "Sending 2",
            "Sending 3",
            "Sending 4"
        )
    }

    @Test
    fun testGuideChannelExample09() {
        test("GuideChannelExample09") { guide.channel.example09.main(emptyArray()) }.verifyLines(
            "ping Ball(hits=1)",
            "pong Ball(hits=2)",
            "ping Ball(hits=3)",
            "pong Ball(hits=4)"
        )
    }

    @Test
    fun testGuideSyncExample01() {
        test("GuideSyncExample01") { guide.sync.example01.main(emptyArray()) }.verifyLinesStart(
            "Completed 1000000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testGuideSyncExample01b() {
        test("GuideSyncExample01b") { guide.sync.example01b.main(emptyArray()) }.verifyLinesStart(
            "Completed 1000000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testGuideSyncExample02() {
        test("GuideSyncExample02") { guide.sync.example02.main(emptyArray()) }.verifyLinesStart(
            "Completed 1000000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testGuideSyncExample03() {
        test("GuideSyncExample03") { guide.sync.example03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testGuideSyncExample04() {
        test("GuideSyncExample04") { guide.sync.example04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testGuideSyncExample05() {
        test("GuideSyncExample05") { guide.sync.example05.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testGuideSyncExample06() {
        test("GuideSyncExample06") { guide.sync.example06.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testGuideSyncExample07() {
        test("GuideSyncExample07") { guide.sync.example07.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 1000000 actions in xxx ms",
            "Counter = 1000000"
        )
    }

    @Test
    fun testGuideSelectExample01() {
        test("GuideSelectExample01") { guide.select.example01.main(emptyArray()) }.verifyLines(
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
    fun testGuideSelectExample02() {
        test("GuideSelectExample02") { guide.select.example02.main(emptyArray()) }.verifyLines(
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
    fun testGuideSelectExample03() {
        test("GuideSelectExample03") { guide.select.example03.main(emptyArray()) }.verifyLines(
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
    fun testGuideSelectExample04() {
        test("GuideSelectExample04") { guide.select.example04.main(emptyArray()) }.verifyLines(
            "Deferred 4 produced answer 'Waited for 128 ms'",
            "11 coroutines are still active"
        )
    }

    @Test
    fun testGuideSelectExample05() {
        test("GuideSelectExample05") { guide.select.example05.main(emptyArray()) }.verifyLines(
            "BEGIN",
            "Replace",
            "END",
            "Channel was closed"
        )
    }
}
