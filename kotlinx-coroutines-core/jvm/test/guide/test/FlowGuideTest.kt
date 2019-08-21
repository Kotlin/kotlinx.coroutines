// This file was automatically generated from flow.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class FlowGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideFlow01() {
        test("KotlinxCoroutinesGuideFlow01") { kotlinx.coroutines.guide.flow01.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow02() {
        test("KotlinxCoroutinesGuideFlow02") { kotlinx.coroutines.guide.flow02.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow03() {
        test("KotlinxCoroutinesGuideFlow03") { kotlinx.coroutines.guide.flow03.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow04() {
        test("KotlinxCoroutinesGuideFlow04") { kotlinx.coroutines.guide.flow04.main() }.verifyLines(
            "I'm not blocked 1",
            "1",
            "I'm not blocked 2",
            "2",
            "I'm not blocked 3",
            "3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow05() {
        test("KotlinxCoroutinesGuideFlow05") { kotlinx.coroutines.guide.flow05.main() }.verifyLines(
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
    fun testKotlinxCoroutinesGuideFlow06() {
        test("KotlinxCoroutinesGuideFlow06") { kotlinx.coroutines.guide.flow06.main() }.verifyLines(
            "Emitting 1",
            "1",
            "Emitting 2",
            "2",
            "Done"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow07() {
        test("KotlinxCoroutinesGuideFlow07") { kotlinx.coroutines.guide.flow07.main() }.verifyLines(
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow08() {
        test("KotlinxCoroutinesGuideFlow08") { kotlinx.coroutines.guide.flow08.main() }.verifyLines(
            "response 1",
            "response 2",
            "response 3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow09() {
        test("KotlinxCoroutinesGuideFlow09") { kotlinx.coroutines.guide.flow09.main() }.verifyLines(
            "Making request 1",
            "response 1",
            "Making request 2",
            "response 2",
            "Making request 3",
            "response 3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow10() {
        test("KotlinxCoroutinesGuideFlow10") { kotlinx.coroutines.guide.flow10.main() }.verifyLines(
            "1",
            "2",
            "Finally in numbers"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow11() {
        test("KotlinxCoroutinesGuideFlow11") { kotlinx.coroutines.guide.flow11.main() }.verifyLines(
            "55"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow12() {
        test("KotlinxCoroutinesGuideFlow12") { kotlinx.coroutines.guide.flow12.main() }.verifyLines(
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
    fun testKotlinxCoroutinesGuideFlow13() {
        test("KotlinxCoroutinesGuideFlow13") { kotlinx.coroutines.guide.flow13.main() }.verifyLinesFlexibleThread(
            "[main @coroutine#1] Started foo flow",
            "[main @coroutine#1] Collected 1",
            "[main @coroutine#1] Collected 2",
            "[main @coroutine#1] Collected 3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow14() {
        test("KotlinxCoroutinesGuideFlow14") { kotlinx.coroutines.guide.flow14.main() }.verifyExceptions(
            "Exception in thread \"main\" java.lang.IllegalStateException: Flow invariant is violated:",
            "		Flow was collected in [CoroutineId(1), \"coroutine#1\":BlockingCoroutine{Active}@5511c7f8, BlockingEventLoop@2eac3323],",
            "		but emission happened in [CoroutineId(1), \"coroutine#1\":DispatchedCoroutine{Active}@2dae0000, DefaultDispatcher].",
            "		Please refer to 'flow' documentation or use 'flowOn' instead",
            "	at ..."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow15() {
        test("KotlinxCoroutinesGuideFlow15") { kotlinx.coroutines.guide.flow15.main() }.verifyLinesFlexibleThread(
            "[DefaultDispatcher-worker-1 @coroutine#2] Emitting 1",
            "[main @coroutine#1] Collected 1",
            "[DefaultDispatcher-worker-1 @coroutine#2] Emitting 2",
            "[main @coroutine#1] Collected 2",
            "[DefaultDispatcher-worker-1 @coroutine#2] Emitting 3",
            "[main @coroutine#1] Collected 3"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow16() {
        test("KotlinxCoroutinesGuideFlow16") { kotlinx.coroutines.guide.flow16.main() }.verifyLinesArbitraryTime(
            "1",
            "2",
            "3",
            "Collected in 1220 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow17() {
        test("KotlinxCoroutinesGuideFlow17") { kotlinx.coroutines.guide.flow17.main() }.verifyLinesArbitraryTime(
            "1",
            "2",
            "3",
            "Collected in 1071 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow18() {
        test("KotlinxCoroutinesGuideFlow18") { kotlinx.coroutines.guide.flow18.main() }.verifyLinesArbitraryTime(
            "1",
            "3",
            "Collected in 758 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow19() {
        test("KotlinxCoroutinesGuideFlow19") { kotlinx.coroutines.guide.flow19.main() }.verifyLinesArbitraryTime(
            "Collecting 1",
            "Collecting 2",
            "Collecting 3",
            "Done 3",
            "Collected in 741 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow20() {
        test("KotlinxCoroutinesGuideFlow20") { kotlinx.coroutines.guide.flow20.main() }.verifyLines(
            "1 -> one",
            "2 -> two",
            "3 -> three"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow21() {
        test("KotlinxCoroutinesGuideFlow21") { kotlinx.coroutines.guide.flow21.main() }.verifyLinesArbitraryTime(
            "1 -> one at 437 ms from start",
            "2 -> two at 837 ms from start",
            "3 -> three at 1243 ms from start"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow22() {
        test("KotlinxCoroutinesGuideFlow22") { kotlinx.coroutines.guide.flow22.main() }.verifyLinesArbitraryTime(
            "1 -> one at 452 ms from start",
            "2 -> one at 651 ms from start",
            "2 -> two at 854 ms from start",
            "3 -> two at 952 ms from start",
            "3 -> three at 1256 ms from start"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow23() {
        test("KotlinxCoroutinesGuideFlow23") { kotlinx.coroutines.guide.flow23.main() }.verifyLinesArbitraryTime(
            "1: First at 121 ms from start",
            "1: Second at 622 ms from start",
            "2: First at 727 ms from start",
            "2: Second at 1227 ms from start",
            "3: First at 1328 ms from start",
            "3: Second at 1829 ms from start"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow24() {
        test("KotlinxCoroutinesGuideFlow24") { kotlinx.coroutines.guide.flow24.main() }.verifyLinesArbitraryTime(
            "1: First at 136 ms from start",
            "2: First at 231 ms from start",
            "3: First at 333 ms from start",
            "1: Second at 639 ms from start",
            "2: Second at 732 ms from start",
            "3: Second at 833 ms from start"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow25() {
        test("KotlinxCoroutinesGuideFlow25") { kotlinx.coroutines.guide.flow25.main() }.verifyLinesArbitraryTime(
            "1: First at 142 ms from start",
            "2: First at 322 ms from start",
            "3: First at 425 ms from start",
            "3: Second at 931 ms from start"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow26() {
        test("KotlinxCoroutinesGuideFlow26") { kotlinx.coroutines.guide.flow26.main() }.verifyLines(
            "Emitting 1",
            "1",
            "Emitting 2",
            "2",
            "Caught java.lang.IllegalStateException: Collected 2"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow27() {
        test("KotlinxCoroutinesGuideFlow27") { kotlinx.coroutines.guide.flow27.main() }.verifyLines(
            "Emitting 1",
            "string 1",
            "Emitting 2",
            "Caught java.lang.IllegalStateException: Crashed on 2"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow28() {
        test("KotlinxCoroutinesGuideFlow28") { kotlinx.coroutines.guide.flow28.main() }.verifyLines(
            "Emitting 1",
            "string 1",
            "Emitting 2",
            "Caught java.lang.IllegalStateException: Crashed on 2"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow29() {
        test("KotlinxCoroutinesGuideFlow29") { kotlinx.coroutines.guide.flow29.main() }.verifyExceptions(
            "Emitting 1",
            "1",
            "Emitting 2",
            "Exception in thread \"main\" java.lang.IllegalStateException: Collected 2",
            "	at ..."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow30() {
        test("KotlinxCoroutinesGuideFlow30") { kotlinx.coroutines.guide.flow30.main() }.verifyExceptions(
            "Emitting 1",
            "1",
            "Emitting 2",
            "Caught java.lang.IllegalStateException: Collected 2"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow31() {
        test("KotlinxCoroutinesGuideFlow31") { kotlinx.coroutines.guide.flow31.main() }.verifyLines(
            "1",
            "2",
            "3",
            "Done"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow32() {
        test("KotlinxCoroutinesGuideFlow32") { kotlinx.coroutines.guide.flow32.main() }.verifyLines(
            "1",
            "2",
            "3",
            "Done"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow33() {
        test("KotlinxCoroutinesGuideFlow33") { kotlinx.coroutines.guide.flow33.main() }.verifyLines(
            "1",
            "Flow completed exceptionally",
            "Caught exception"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow34() {
        test("KotlinxCoroutinesGuideFlow34") { kotlinx.coroutines.guide.flow34.main() }.verifyExceptions(
            "1",
            "Flow completed with null",
            "Exception in thread \"main\" java.lang.IllegalStateException: Collected 2"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow35() {
        test("KotlinxCoroutinesGuideFlow35") { kotlinx.coroutines.guide.flow35.main() }.verifyLines(
            "Event: 1",
            "Event: 2",
            "Event: 3",
            "Done"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideFlow36() {
        test("KotlinxCoroutinesGuideFlow36") { kotlinx.coroutines.guide.flow36.main() }.verifyLines(
            "Done",
            "Event: 1",
            "Event: 2",
            "Event: 3"
        )
    }
}
