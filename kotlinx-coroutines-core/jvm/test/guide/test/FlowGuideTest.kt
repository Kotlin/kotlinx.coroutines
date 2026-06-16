// This file was automatically generated from coroutines-flow-operators.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class FlowGuideTest {
    @Test
    fun testExampleFlow01() {
        test("ExampleFlow01") { kotlinx.coroutines.guide.exampleFlow01.main() }.verifyLines(
            "response 1",
            "response 2",
            "response 3"
        )
    }

    @Test
    fun testExampleFlow02() {
        test("ExampleFlow02") { kotlinx.coroutines.guide.exampleFlow02.main() }.verifyLines(
            "Making request 1",
            "response 1",
            "Making request 2",
            "response 2",
            "Making request 3",
            "response 3"
        )
    }

    @Test
    fun testExampleFlow03() {
        test("ExampleFlow03") { kotlinx.coroutines.guide.exampleFlow03.main() }.verifyLines(
            "1",
            "2",
            "Finally in numbers"
        )
    }

    @Test
    fun testExampleFlow04() {
        test("ExampleFlow04") { kotlinx.coroutines.guide.exampleFlow04.main() }.verifyLines(
            "55"
        )
    }

    @Test
    fun testExampleFlow05() {
        test("ExampleFlow05") { kotlinx.coroutines.guide.exampleFlow05.main() }.verifyLinesArbitraryTime(
            "1",
            "2",
            "3",
            "Collected in 1220 ms"
        )
    }

    @Test
    fun testExampleFlow06() {
        test("ExampleFlow06") { kotlinx.coroutines.guide.exampleFlow06.main() }.verifyLinesArbitraryTime(
            "1",
            "2",
            "3",
            "Collected in 1071 ms"
        )
    }

    @Test
    fun testExampleFlow07() {
        test("ExampleFlow07") { kotlinx.coroutines.guide.exampleFlow07.main() }.verifyLinesArbitraryTime(
            "1",
            "3",
            "Collected in 758 ms"
        )
    }

    @Test
    fun testExampleFlow08() {
        test("ExampleFlow08") { kotlinx.coroutines.guide.exampleFlow08.main() }.verifyLinesArbitraryTime(
            "Collecting 1",
            "Collecting 2",
            "Collecting 3",
            "Done 3",
            "Collected in 741 ms"
        )
    }

    @Test
    fun testExampleFlow09() {
        test("ExampleFlow09") { kotlinx.coroutines.guide.exampleFlow09.main() }.verifyLines(
            "1 -> one",
            "2 -> two",
            "3 -> three"
        )
    }

    @Test
    fun testExampleFlow10() {
        test("ExampleFlow10") { kotlinx.coroutines.guide.exampleFlow10.main() }.verifyLinesArbitraryTime(
            "1 -> one at 437 ms from start",
            "2 -> two at 837 ms from start",
            "3 -> three at 1243 ms from start"
        )
    }

    @Test
    fun testExampleFlow11() {
        test("ExampleFlow11") { kotlinx.coroutines.guide.exampleFlow11.main() }.verifyLinesArbitraryTime(
            "1 -> one at 452 ms from start",
            "2 -> one at 651 ms from start",
            "2 -> two at 854 ms from start",
            "3 -> two at 952 ms from start",
            "3 -> three at 1256 ms from start"
        )
    }

    @Test
    fun testExampleFlow12() {
        test("ExampleFlow12") { kotlinx.coroutines.guide.exampleFlow12.main() }.verifyLinesArbitraryTime(
            "1: First at 121 ms from start",
            "1: Second at 622 ms from start",
            "2: First at 727 ms from start",
            "2: Second at 1227 ms from start",
            "3: First at 1328 ms from start",
            "3: Second at 1829 ms from start"
        )
    }

    @Test
    fun testExampleFlow13() {
        test("ExampleFlow13") { kotlinx.coroutines.guide.exampleFlow13.main() }.verifyLinesArbitraryTime(
            "1: First at 136 ms from start",
            "2: First at 231 ms from start",
            "3: First at 333 ms from start",
            "1: Second at 639 ms from start",
            "2: Second at 732 ms from start",
            "3: Second at 833 ms from start"
        )
    }

    @Test
    fun testExampleFlow14() {
        test("ExampleFlow14") { kotlinx.coroutines.guide.exampleFlow14.main() }.verifyLinesArbitraryTime(
            "1: First at 142 ms from start",
            "2: First at 322 ms from start",
            "3: First at 425 ms from start",
            "3: Second at 931 ms from start"
        )
    }

    @Test
    fun testExampleFlow15() {
        test("ExampleFlow15") { kotlinx.coroutines.guide.exampleFlow15.main() }.verifyLines(
            "1",
            "2",
            "3",
            "Done"
        )
    }

    @Test
    fun testExampleFlow16() {
        test("ExampleFlow16") { kotlinx.coroutines.guide.exampleFlow16.main() }.verifyLines(
            "1",
            "2",
            "3",
            "Done"
        )
    }

    @Test
    fun testExampleFlow17() {
        test("ExampleFlow17") { kotlinx.coroutines.guide.exampleFlow17.main() }.verifyLines(
            "1",
            "Flow completed exceptionally",
            "Caught exception"
        )
    }

    @Test
    fun testExampleFlow18() {
        test("ExampleFlow18") { kotlinx.coroutines.guide.exampleFlow18.main() }.verifyExceptions(
            "1",
            "Flow completed with java.lang.IllegalStateException: Collected 2",
            "Exception in thread \"main\" java.lang.IllegalStateException: Collected 2"
        )
    }

    @Test
    fun testExampleFlow19() {
        test("ExampleFlow19") { kotlinx.coroutines.guide.exampleFlow19.main() }.verifyLines(
            "Event: 1",
            "Event: 2",
            "Event: 3",
            "Done"
        )
    }

    @Test
    fun testExampleFlow20() {
        test("ExampleFlow20") { kotlinx.coroutines.guide.exampleFlow20.main() }.verifyLines(
            "Done",
            "Event: 1",
            "Event: 2",
            "Event: 3"
        )
    }
}
