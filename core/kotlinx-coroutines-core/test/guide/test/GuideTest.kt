// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class GuideTest {

    @Test
    fun testKotlinxCoroutinesGuideBasic01() {
        test("KotlinxCoroutinesGuideBasic01") { kotlinx.coroutines.guide.basic01.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic02() {
        test("KotlinxCoroutinesGuideBasic02") { kotlinx.coroutines.guide.basic02.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic02b() {
        test("KotlinxCoroutinesGuideBasic02b") { kotlinx.coroutines.guide.basic02b.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic03() {
        test("KotlinxCoroutinesGuideBasic03") { kotlinx.coroutines.guide.basic03.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic03s() {
        test("KotlinxCoroutinesGuideBasic03s") { kotlinx.coroutines.guide.basic03s.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic04() {
        test("KotlinxCoroutinesGuideBasic04") { kotlinx.coroutines.guide.basic04.main(emptyArray()) }.verifyLines(
            "Task from coroutine scope",
            "Task from runBlocking",
            "Task from nested launch",
            "Coroutine scope is over"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic05() {
        test("KotlinxCoroutinesGuideBasic05") { kotlinx.coroutines.guide.basic05.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic05s() {
        test("KotlinxCoroutinesGuideBasic05s") { kotlinx.coroutines.guide.basic05s.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic06() {
        test("KotlinxCoroutinesGuideBasic06") { kotlinx.coroutines.guide.basic06.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0] == ".".repeat(100_000))
        }
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic07() {
        test("KotlinxCoroutinesGuideBasic07") { kotlinx.coroutines.guide.basic07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ..."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel01() {
        test("KotlinxCoroutinesGuideCancel01") { kotlinx.coroutines.guide.cancel01.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel02() {
        test("KotlinxCoroutinesGuideCancel02") { kotlinx.coroutines.guide.cancel02.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesGuideCancel03() {
        test("KotlinxCoroutinesGuideCancel03") { kotlinx.coroutines.guide.cancel03.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel04() {
        test("KotlinxCoroutinesGuideCancel04") { kotlinx.coroutines.guide.cancel04.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm running finally",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel05() {
        test("KotlinxCoroutinesGuideCancel05") { kotlinx.coroutines.guide.cancel05.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesGuideCancel06() {
        test("KotlinxCoroutinesGuideCancel06") { kotlinx.coroutines.guide.cancel06.main(emptyArray()) }.verifyLinesStartWith(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Exception in thread \"main\" kotlinx.coroutines.TimeoutCancellationException: Timed out waiting for 1300 MILLISECONDS"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel07() {
        test("KotlinxCoroutinesGuideCancel07") { kotlinx.coroutines.guide.cancel07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Result is null"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCompose01() {
        test("KotlinxCoroutinesGuideCompose01") { kotlinx.coroutines.guide.compose01.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 2017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCompose02() {
        test("KotlinxCoroutinesGuideCompose02") { kotlinx.coroutines.guide.compose02.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCompose03() {
        test("KotlinxCoroutinesGuideCompose03") { kotlinx.coroutines.guide.compose03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCompose04() {
        test("KotlinxCoroutinesGuideCompose04") { kotlinx.coroutines.guide.compose04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1085 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCompose05() {
        test("KotlinxCoroutinesGuideCompose05") { kotlinx.coroutines.guide.compose05.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCompose06() {
        test("KotlinxCoroutinesGuideCompose06") { kotlinx.coroutines.guide.compose06.main(emptyArray()) }.verifyLines(
            "Second child throws an exception",
            "First child was cancelled",
            "Computation failed with ArithmeticException"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext01() {
        test("KotlinxCoroutinesGuideContext01") { kotlinx.coroutines.guide.context01.main(emptyArray()) }.verifyLinesStartUnordered(
            "Unconfined            : I'm working in thread main",
            "Default               : I'm working in thread CommonPool-worker-1",
            "newSingleThreadContext: I'm working in thread MyOwnThread",
            "main runBlocking      : I'm working in thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext02() {
        test("KotlinxCoroutinesGuideContext02") { kotlinx.coroutines.guide.context02.main(emptyArray()) }.verifyLinesStart(
            "Unconfined      : I'm working in thread main",
            "main runBlocking: I'm working in thread main",
            "Unconfined      : After delay in thread kotlinx.coroutines.DefaultExecutor",
            "main runBlocking: After delay in thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext03() {
        test("KotlinxCoroutinesGuideContext03") { kotlinx.coroutines.guide.context03.main(emptyArray()) }.verifyLinesFlexibleThread(
            "[main @coroutine#2] I'm computing a piece of the answer",
            "[main @coroutine#3] I'm computing another piece of the answer",
            "[main @coroutine#1] The answer is 42"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext04() {
        test("KotlinxCoroutinesGuideContext04") { kotlinx.coroutines.guide.context04.main(emptyArray()) }.verifyLines(
            "[Ctx1 @coroutine#1] Started in ctx1",
            "[Ctx2 @coroutine#1] Working in ctx2",
            "[Ctx1 @coroutine#1] Back to ctx1"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext05() {
        test("KotlinxCoroutinesGuideContext05") { kotlinx.coroutines.guide.context05.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0].startsWith("My job is \"coroutine#1\":BlockingCoroutine{Active}@"))
        }
    }

    @Test
    fun testKotlinxCoroutinesGuideContext06() {
        test("KotlinxCoroutinesGuideContext06") { kotlinx.coroutines.guide.context06.main(emptyArray()) }.verifyLines(
            "job1: I run in GlobalScope and execute independently!",
            "job2: I am a child of the request coroutine",
            "job1: I am not affected by cancellation of the request",
            "main: Who has survived request cancellation?"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext07() {
        test("KotlinxCoroutinesGuideContext07") { kotlinx.coroutines.guide.context07.main(emptyArray()) }.verifyLines(
            "request: I'm done and I don't explicitly join my children that are still active",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Coroutine 2 is done",
            "Now processing of the request is complete"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext08() {
        test("KotlinxCoroutinesGuideContext08") { kotlinx.coroutines.guide.context08.main(emptyArray()) }.verifyLinesFlexibleThread(
            "[main @main#1] Started main coroutine",
            "[main @v1coroutine#2] Computing v1",
            "[main @v2coroutine#3] Computing v2",
            "[main @main#1] The answer for v1 / v2 = 42"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext09() {
        test("KotlinxCoroutinesGuideContext09") { kotlinx.coroutines.guide.context09.main(emptyArray()) }.verifyLinesFlexibleThread(
            "I'm working in thread CommonPool-worker-1 @test#2"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext10() {
        test("KotlinxCoroutinesGuideContext10") { kotlinx.coroutines.guide.context10.main(emptyArray()) }.verifyLines(
            "Launched coroutines",
            "Coroutine 0 is done",
            "Coroutine 1 is done",
            "Destroying activity!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideContext11() {
        test("KotlinxCoroutinesGuideContext11") { kotlinx.coroutines.guide.context11.main(emptyArray()) }.verifyLinesFlexibleThread(
            "Pre-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'",
            "Launch start, current thread: Thread[CommonPool-worker-1 @coroutine#2,5,main], thread local value: 'launch'",
            "After yield, current thread: Thread[CommonPool-worker-2 @coroutine#2,5,main], thread local value: 'launch'",
            "Post-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions01() {
        test("KotlinxCoroutinesGuideExceptions01") { kotlinx.coroutines.guide.exceptions01.main(emptyArray()) }.verifyExceptions(
            "Throwing exception from launch",
            "Exception in thread \"ForkJoinPool.commonPool-worker-2 @coroutine#2\" java.lang.IndexOutOfBoundsException",
            "Joined failed job",
            "Throwing exception from async",
            "Caught ArithmeticException"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions02() {
        test("KotlinxCoroutinesGuideExceptions02") { kotlinx.coroutines.guide.exceptions02.main(emptyArray()) }.verifyLines(
            "Caught java.lang.AssertionError"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions03() {
        test("KotlinxCoroutinesGuideExceptions03") { kotlinx.coroutines.guide.exceptions03.main(emptyArray()) }.verifyLines(
            "Cancelling child",
            "Child is cancelled",
            "Parent is not cancelled"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions04() {
        test("KotlinxCoroutinesGuideExceptions04") { kotlinx.coroutines.guide.exceptions04.main(emptyArray()) }.verifyLines(
            "Second child throws an exception",
            "Children are cancelled, but exception is not handled until all children terminate",
            "The first child finished its non cancellable block",
            "Caught java.lang.ArithmeticException"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions05() {
        test("KotlinxCoroutinesGuideExceptions05") { kotlinx.coroutines.guide.exceptions05.main(emptyArray()) }.verifyLines(
            "Caught java.io.IOException with suppressed [java.lang.ArithmeticException]"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions06() {
        test("KotlinxCoroutinesGuideExceptions06") { kotlinx.coroutines.guide.exceptions06.main(emptyArray()) }.verifyLines(
            "Rethrowing JobCancellationException with original cause",
            "Caught original java.io.IOException"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel01() {
        test("KotlinxCoroutinesGuideChannel01") { kotlinx.coroutines.guide.channel01.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel02() {
        test("KotlinxCoroutinesGuideChannel02") { kotlinx.coroutines.guide.channel02.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel03() {
        test("KotlinxCoroutinesGuideChannel03") { kotlinx.coroutines.guide.channel03.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel04() {
        test("KotlinxCoroutinesGuideChannel04") { kotlinx.coroutines.guide.channel04.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel05() {
        test("KotlinxCoroutinesGuideChannel05") { kotlinx.coroutines.guide.channel05.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesGuideChannel06() {
        test("KotlinxCoroutinesGuideChannel06") { kotlinx.coroutines.guide.channel06.main(emptyArray()) }.also { lines ->
            check(lines.size == 10 && lines.withIndex().all { (i, line) -> line.startsWith("Processor #") && line.endsWith(" received ${i + 1}") })
        }
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel07() {
        test("KotlinxCoroutinesGuideChannel07") { kotlinx.coroutines.guide.channel07.main(emptyArray()) }.verifyLines(
            "foo",
            "foo",
            "BAR!",
            "foo",
            "foo",
            "BAR!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel08() {
        test("KotlinxCoroutinesGuideChannel08") { kotlinx.coroutines.guide.channel08.main(emptyArray()) }.verifyLines(
            "Sending 0",
            "Sending 1",
            "Sending 2",
            "Sending 3",
            "Sending 4"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel09() {
        test("KotlinxCoroutinesGuideChannel09") { kotlinx.coroutines.guide.channel09.main(emptyArray()) }.verifyLines(
            "ping Ball(hits=1)",
            "pong Ball(hits=2)",
            "ping Ball(hits=3)",
            "pong Ball(hits=4)"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel10() {
        test("KotlinxCoroutinesGuideChannel10") { kotlinx.coroutines.guide.channel10.main(emptyArray()) }.verifyLines(
            "Initial element is available immediately: kotlin.Unit",
            "Next element is not ready in 50 ms: null",
            "Next element is ready in 100 ms: kotlin.Unit",
            "Consumer pauses for 150ms",
            "Next element is available immediately after large consumer delay: kotlin.Unit",
            "Next element is ready in 50ms after consumer pause in 150ms: kotlin.Unit"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync01() {
        test("KotlinxCoroutinesGuideSync01") { kotlinx.coroutines.guide.sync01.main(emptyArray()) }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync01b() {
        test("KotlinxCoroutinesGuideSync01b") { kotlinx.coroutines.guide.sync01b.main(emptyArray()) }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync02() {
        test("KotlinxCoroutinesGuideSync02") { kotlinx.coroutines.guide.sync02.main(emptyArray()) }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync03() {
        test("KotlinxCoroutinesGuideSync03") { kotlinx.coroutines.guide.sync03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync04() {
        test("KotlinxCoroutinesGuideSync04") { kotlinx.coroutines.guide.sync04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync05() {
        test("KotlinxCoroutinesGuideSync05") { kotlinx.coroutines.guide.sync05.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync06() {
        test("KotlinxCoroutinesGuideSync06") { kotlinx.coroutines.guide.sync06.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync07() {
        test("KotlinxCoroutinesGuideSync07") { kotlinx.coroutines.guide.sync07.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSelect01() {
        test("KotlinxCoroutinesGuideSelect01") { kotlinx.coroutines.guide.select01.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesGuideSelect02() {
        test("KotlinxCoroutinesGuideSelect02") { kotlinx.coroutines.guide.select02.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesGuideSelect03() {
        test("KotlinxCoroutinesGuideSelect03") { kotlinx.coroutines.guide.select03.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesGuideSelect04() {
        test("KotlinxCoroutinesGuideSelect04") { kotlinx.coroutines.guide.select04.main(emptyArray()) }.verifyLines(
            "Deferred 4 produced answer 'Waited for 128 ms'",
            "11 coroutines are still active"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSelect05() {
        test("KotlinxCoroutinesGuideSelect05") { kotlinx.coroutines.guide.select05.main(emptyArray()) }.verifyLines(
            "BEGIN",
            "Replace",
            "END",
            "Channel was closed"
        )
    }
}
