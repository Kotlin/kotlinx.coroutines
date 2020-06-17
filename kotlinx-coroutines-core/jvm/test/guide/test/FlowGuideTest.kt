/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from flow.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class FlowGuideTest {
    @Test
    fun testExampleFlow01() {
        test("ExampleFlow01") { kotlinx.coroutines.guide.exampleFlow01.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testExampleFlow02() {
        test("ExampleFlow02") { kotlinx.coroutines.guide.exampleFlow02.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testExampleFlow03() {
        test("ExampleFlow03") { kotlinx.coroutines.guide.exampleFlow03.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testExampleFlow04() {
        test("ExampleFlow04") { kotlinx.coroutines.guide.exampleFlow04.main() }.verifyLines(
            "I'm not blocked 1",
            "1",
            "I'm not blocked 2",
            "2",
            "I'm not blocked 3",
            "3"
        )
    }

    @Test
    fun testExampleFlow05() {
        test("ExampleFlow05") { kotlinx.coroutines.guide.exampleFlow05.main() }.verifyLines(
            "Calling foo...",
            "Calling collect...",
            "Flow started",
            "1",
            "2",
            "3",
            "Calling collect again...",
            "Flow started",
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testExampleFlow06() {
        test("ExampleFlow06") { kotlinx.coroutines.guide.exampleFlow06.main() }.verifyLines(
            "Emitting 1",
            "1",
            "Emitting 2",
            "2",
            "Done"
        )
    }

    @Test
    fun testExampleFlow07() {
        test("ExampleFlow07") { kotlinx.coroutines.guide.exampleFlow07.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testExampleFlow08() {
        test("ExampleFlow08") { kotlinx.coroutines.guide.exampleFlow08.main() }.verifyLines(
            "response 1",
            "response 2",
            "response 3"
        )
    }

    @Test
    fun testExampleFlow09() {
        test("ExampleFlow09") { kotlinx.coroutines.guide.exampleFlow09.main() }.verifyLines(
            "Making request 1",
            "response 1",
            "Making request 2",
            "response 2",
            "Making request 3",
            "response 3"
        )
    }

    @Test
    fun testExampleFlow10() {
        test("ExampleFlow10") { kotlinx.coroutines.guide.exampleFlow10.main() }.verifyLines(
            "1",
            "2",
            "Finally in numbers"
        )
    }

    @Test
    fun testExampleFlow11() {
        test("ExampleFlow11") { kotlinx.coroutines.guide.exampleFlow11.main() }.verifyLines(
            "55"
        )
    }

    @Test
    fun testExampleFlow12() {
        test("ExampleFlow12") { kotlinx.coroutines.guide.exampleFlow12.main() }.verifyLines(
            "Filter 1",
            "Filter 2",
            "Map 2",
            "Collect string 2",
            "Filter 3",
            "Filter 4",
            "Map 4",
            "Collect string 4",
            "Filter 5"
        )
    }

    @Test
    fun testExampleFlow13() {
        test("ExampleFlow13") { kotlinx.coroutines.guide.exampleFlow13.main() }.verifyLinesFlexibleThread(
            "[main @coroutine#1] Started foo flow",
            "[main @coroutine#1] Collected 1",
            "[main @coroutine#1] Collected 2",
            "[main @coroutine#1] Collected 3"
        )
    }

    @Test
    fun testExampleFlow14() {
        test("ExampleFlow14") { kotlinx.coroutines.guide.exampleFlow14.main() }.verifyExceptions(
            "Exception in thread \"main\" java.lang.IllegalStateException: Flow invariant is violated:",
            "\t\tFlow was collected in [CoroutineId(1), \"coroutine#1\":BlockingCoroutine{Active}@5511c7f8, BlockingEventLoop@2eac3323],",
            "\t\tbut emission happened in [CoroutineId(1), \"coroutine#1\":DispatchedCoroutine{Active}@2dae0000, Dispatchers.Default].",
            "\t\tPlease refer to 'flow' documentation or use 'flowOn' instead",
            "\tat ..."
        )
    }

    @Test
    fun testExampleFlow15() {
        test("ExampleFlow15") { kotlinx.coroutines.guide.exampleFlow15.main() }.verifyLinesFlexibleThread(
            "[DefaultDispatcher-worker-1 @coroutine#2] Emitting 1",
            "[main @coroutine#1] Collected 1",
            "[DefaultDispatcher-worker-1 @coroutine#2] Emitting 2",
            "[main @coroutine#1] Collected 2",
            "[DefaultDispatcher-worker-1 @coroutine#2] Emitting 3",
            "[main @coroutine#1] Collected 3"
        )
    }

    @Test
    fun testExampleFlow16() {
        test("ExampleFlow16") { kotlinx.coroutines.guide.exampleFlow16.main() }.verifyLinesArbitraryTime(
            "1",
            "2",
            "3",
            "Collected in 1220 ms"
        )
    }

    @Test
    fun testExampleFlow17() {
        test("ExampleFlow17") { kotlinx.coroutines.guide.exampleFlow17.main() }.verifyLinesArbitraryTime(
            "1",
            "2",
            "3",
            "Collected in 1071 ms"
        )
    }

    @Test
    fun testExampleFlow18() {
        test("ExampleFlow18") { kotlinx.coroutines.guide.exampleFlow18.main() }.verifyLinesArbitraryTime(
            "1",
            "3",
            "Collected in 758 ms"
        )
    }

    @Test
    fun testExampleFlow19() {
        test("ExampleFlow19") { kotlinx.coroutines.guide.exampleFlow19.main() }.verifyLinesArbitraryTime(
            "Collecting 1",
            "Collecting 2",
            "Collecting 3",
            "Done 3",
            "Collected in 741 ms"
        )
    }

    @Test
    fun testExampleFlow20() {
        test("ExampleFlow20") { kotlinx.coroutines.guide.exampleFlow20.main() }.verifyLines(
            "1 -> one",
            "2 -> two",
            "3 -> three"
        )
    }

    @Test
    fun testExampleFlow21() {
        test("ExampleFlow21") { kotlinx.coroutines.guide.exampleFlow21.main() }.verifyLinesArbitraryTime(
            "1 -> one at 437 ms from start",
            "2 -> two at 837 ms from start",
            "3 -> three at 1243 ms from start"
        )
    }

    @Test
    fun testExampleFlow22() {
        test("ExampleFlow22") { kotlinx.coroutines.guide.exampleFlow22.main() }.verifyLinesArbitraryTime(
            "1 -> one at 452 ms from start",
            "2 -> one at 651 ms from start",
            "2 -> two at 854 ms from start",
            "3 -> two at 952 ms from start",
            "3 -> three at 1256 ms from start"
        )
    }

    @Test
    fun testExampleFlow23() {
        test("ExampleFlow23") { kotlinx.coroutines.guide.exampleFlow23.main() }.verifyLinesArbitraryTime(
            "1: First at 121 ms from start",
            "1: Second at 622 ms from start",
            "2: First at 727 ms from start",
            "2: Second at 1227 ms from start",
            "3: First at 1328 ms from start",
            "3: Second at 1829 ms from start"
        )
    }

    @Test
    fun testExampleFlow24() {
        test("ExampleFlow24") { kotlinx.coroutines.guide.exampleFlow24.main() }.verifyLinesArbitraryTime(
            "1: First at 136 ms from start",
            "2: First at 231 ms from start",
            "3: First at 333 ms from start",
            "1: Second at 639 ms from start",
            "2: Second at 732 ms from start",
            "3: Second at 833 ms from start"
        )
    }

    @Test
    fun testExampleFlow25() {
        test("ExampleFlow25") { kotlinx.coroutines.guide.exampleFlow25.main() }.verifyLinesArbitraryTime(
            "1: First at 142 ms from start",
            "2: First at 322 ms from start",
            "3: First at 425 ms from start",
            "3: Second at 931 ms from start"
        )
    }

    @Test
    fun testExampleFlow26() {
        test("ExampleFlow26") { kotlinx.coroutines.guide.exampleFlow26.main() }.verifyLines(
            "Emitting 1",
            "1",
            "Emitting 2",
            "2",
            "Caught java.lang.IllegalStateException: Collected 2"
        )
    }

    @Test
    fun testExampleFlow27() {
        test("ExampleFlow27") { kotlinx.coroutines.guide.exampleFlow27.main() }.verifyLines(
            "Emitting 1",
            "string 1",
            "Emitting 2",
            "Caught java.lang.IllegalStateException: Crashed on 2"
        )
    }

    @Test
    fun testExampleFlow28() {
        test("ExampleFlow28") { kotlinx.coroutines.guide.exampleFlow28.main() }.verifyLines(
            "Emitting 1",
            "string 1",
            "Emitting 2",
            "Caught java.lang.IllegalStateException: Crashed on 2"
        )
    }

    @Test
    fun testExampleFlow29() {
        test("ExampleFlow29") { kotlinx.coroutines.guide.exampleFlow29.main() }.verifyExceptions(
            "Emitting 1",
            "1",
            "Emitting 2",
            "Exception in thread \"main\" java.lang.IllegalStateException: Collected 2",
            "\tat ..."
        )
    }

    @Test
    fun testExampleFlow30() {
        test("ExampleFlow30") { kotlinx.coroutines.guide.exampleFlow30.main() }.verifyExceptions(
            "Emitting 1",
            "1",
            "Emitting 2",
            "Caught java.lang.IllegalStateException: Collected 2"
        )
    }

    @Test
    fun testExampleFlow31() {
        test("ExampleFlow31") { kotlinx.coroutines.guide.exampleFlow31.main() }.verifyLines(
            "1",
            "2",
            "3",
            "Done"
        )
    }

    @Test
    fun testExampleFlow32() {
        test("ExampleFlow32") { kotlinx.coroutines.guide.exampleFlow32.main() }.verifyLines(
            "1",
            "2",
            "3",
            "Done"
        )
    }

    @Test
    fun testExampleFlow33() {
        test("ExampleFlow33") { kotlinx.coroutines.guide.exampleFlow33.main() }.verifyLines(
            "1",
            "Flow completed exceptionally",
            "Caught exception"
        )
    }

    @Test
    fun testExampleFlow34() {
        test("ExampleFlow34") { kotlinx.coroutines.guide.exampleFlow34.main() }.verifyExceptions(
            "1",
            "Flow completed with java.lang.IllegalStateException: Collected 2",
            "Exception in thread \"main\" java.lang.IllegalStateException: Collected 2"
        )
    }

    @Test
    fun testExampleFlow35() {
        test("ExampleFlow35") { kotlinx.coroutines.guide.exampleFlow35.main() }.verifyLines(
            "Event: 1",
            "Event: 2",
            "Event: 3",
            "Done"
        )
    }

    @Test
    fun testExampleFlow36() {
        test("ExampleFlow36") { kotlinx.coroutines.guide.exampleFlow36.main() }.verifyLines(
            "Done",
            "Event: 1",
            "Event: 2",
            "Event: 3"
        )
    }

    @Test
    fun testExampleFlow37() {
        test("ExampleFlow37") { kotlinx.coroutines.guide.exampleFlow37.main() }.verifyExceptions(
            "Emitting 1",
            "1",
            "Emitting 2",
            "2",
            "Emitting 3",
            "3",
            "Emitting 4",
            "Exception in thread \"main\" kotlinx.coroutines.JobCancellationException: BlockingCoroutine was cancelled; job=\"coroutine#1\":BlockingCoroutine{Cancelled}@6d7b4f4c"
        )
    }

    @Test
    fun testExampleFlow38() {
        test("ExampleFlow38") { kotlinx.coroutines.guide.exampleFlow38.main() }.verifyExceptions(
            "1",
            "2",
            "3",
            "4",
            "5",
            "Exception in thread \"main\" kotlinx.coroutines.JobCancellationException: BlockingCoroutine was cancelled; job=\"coroutine#1\":BlockingCoroutine{Cancelled}@3327bd23"
        )
    }

    @Test
    fun testExampleFlow39() {
        test("ExampleFlow39") { kotlinx.coroutines.guide.exampleFlow39.main() }.verifyExceptions(
            "1",
            "2",
            "3",
            "Exception in thread \"main\" kotlinx.coroutines.JobCancellationException: BlockingCoroutine was cancelled; job=\"coroutine#1\":BlockingCoroutine{Cancelled}@5ec0a365"
        )
    }
}
