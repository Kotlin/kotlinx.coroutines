// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package guide.test

import org.junit.Test

class GuideReactiveTest {

    @Test
    fun testGuideReactiveBasicExample01() {
        test("GuideReactiveBasicExample01") { guide.reactive.basic.example01.main(emptyArray()) }.verifyLines(
            "Elements:",
            "Begin",
            "1",
            "2",
            "3",
            "Again:"
        )
    }

    @Test
    fun testGuideReactiveBasicExample02() {
        test("GuideReactiveBasicExample02") { guide.reactive.basic.example02.main(emptyArray()) }.verifyLines(
            "Elements:",
            "Begin",
            "1",
            "2",
            "3",
            "Again:",
            "Begin",
            "1",
            "2",
            "3"
        )
    }

    @Test
    fun testGuideReactiveBasicExample03() {
        test("GuideReactiveBasicExample03") { guide.reactive.basic.example03.main(emptyArray()) }.verifyLines(
            "OnSubscribe",
            "1",
            "2",
            "3",
            "Finally"
        )
    }

    @Test
    fun testGuideReactiveBasicExample04() {
        test("GuideReactiveBasicExample04") { guide.reactive.basic.example04.main(emptyArray()) }.verifyLines(
            "OnSubscribe",
            "1",
            "2",
            "3",
            "4",
            "Finally",
            "5"
        )
    }

    @Test
    fun testGuideReactiveBasicExample05() {
        test("GuideReactiveBasicExample05") { guide.reactive.basic.example05.main(emptyArray()) }.verifyLines(
            "Sent 1",
            "Processed 1",
            "Sent 2",
            "Processed 2",
            "Sent 3",
            "Processed 3",
            "Complete"
        )
    }

    @Test
    fun testGuideReactiveBasicExample06() {
        test("GuideReactiveBasicExample06") { guide.reactive.basic.example06.main(emptyArray()) }.verifyLines(
            "two",
            "three",
            "four"
        )
    }

    @Test
    fun testGuideReactiveBasicExample07() {
        test("GuideReactiveBasicExample07") { guide.reactive.basic.example07.main(emptyArray()) }.verifyLines(
            "two",
            "three",
            "four"
        )
    }

    @Test
    fun testGuideReactiveBasicExample08() {
        test("GuideReactiveBasicExample08") { guide.reactive.basic.example08.main(emptyArray()) }.verifyLines(
            "four"
        )
    }

    @Test
    fun testGuideReactiveBasicExample09() {
        test("GuideReactiveBasicExample09") { guide.reactive.basic.example09.main(emptyArray()) }.verifyLines(
            "four"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample01() {
        test("GuideReactiveOperatorsExample01") { guide.reactive.operators.example01.main(emptyArray()) }.verifyLines(
            "1",
            "2",
            "3",
            "4",
            "5"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample02() {
        test("GuideReactiveOperatorsExample02") { guide.reactive.operators.example02.main(emptyArray()) }.verifyLines(
            "2 is even",
            "4 is even"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample03() {
        test("GuideReactiveOperatorsExample03") { guide.reactive.operators.example03.main(emptyArray()) }.verifyLines(
            "1",
            "2"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample04() {
        test("GuideReactiveOperatorsExample04") { guide.reactive.operators.example04.main(emptyArray()) }.verifyLines(
            "1",
            "2",
            "11",
            "3",
            "4",
            "12"
        )
    }

    @Test
    fun testGuideReactiveContextExample01() {
        test("GuideReactiveContextExample01") { guide.reactive.context.example01.main(emptyArray()) }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testGuideReactiveContextExample02() {
        test("GuideReactiveContextExample02") { guide.reactive.context.example02.main(emptyArray()) }.verifyLinesStart(
            "1 on thread ForkJoinPool.commonPool-worker-1",
            "2 on thread ForkJoinPool.commonPool-worker-1",
            "3 on thread ForkJoinPool.commonPool-worker-1"
        )
    }

    @Test
    fun testGuideReactiveContextExample03() {
        test("GuideReactiveContextExample03") { guide.reactive.context.example03.main(emptyArray()) }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testGuideReactiveContextExample04() {
        test("GuideReactiveContextExample04") { guide.reactive.context.example04.main(emptyArray()) }.verifyLinesStart(
            "1 on thread main",
            "2 on thread main",
            "3 on thread main"
        )
    }

    @Test
    fun testGuideReactiveContextExample05() {
        test("GuideReactiveContextExample05") { guide.reactive.context.example05.main(emptyArray()) }.verifyLinesStart(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }
}
