// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package guide.test

import org.junit.Test

class GuideReactiveTest {

    @Test
    fun testGuideReactiveBasicExample01() {
        test { guide.reactive.basic.example01.main(emptyArray()) }.verifyLines(
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
        test { guide.reactive.basic.example02.main(emptyArray()) }.verifyLines(
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
        test { guide.reactive.basic.example03.main(emptyArray()) }.verifyLines(
            "OnSubscribe",
            "1",
            "2",
            "3",
            "Finally"
        )
    }

    @Test
    fun testGuideReactiveBasicExample04() {
        test { guide.reactive.basic.example04.main(emptyArray()) }.verifyLines(
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
        test { guide.reactive.basic.example05.main(emptyArray()) }.verifyLines(
            "Sending 1 ...",
            "Sending 2 ...",
            "Received 1",
            "Sending 3 ...",
            "Received 2",
            "Sending 4 ...",
            "Received 3",
            "Sending 5 ...",
            "Received 4",
            "Received 5",
            "Complete"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample01() {
        test { guide.reactive.operators.example01.main(emptyArray()) }.verifyLines(
            "1",
            "2",
            "3",
            "4",
            "5"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample02() {
        test { guide.reactive.operators.example02.main(emptyArray()) }.verifyLines(
            "2 is even",
            "4 is even"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample03() {
        test { guide.reactive.operators.example03.main(emptyArray()) }.verifyLines(
            "1",
            "2"
        )
    }

    @Test
    fun testGuideReactiveOperatorsExample04() {
        test { guide.reactive.operators.example04.main(emptyArray()) }.verifyLines(
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
        test { guide.reactive.context.example01.main(emptyArray()) }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testGuideReactiveContextExample02() {
        test { guide.reactive.context.example02.main(emptyArray()) }.verifyLinesStart(
            "1 on thread ForkJoinPool.commonPool-worker-1",
            "2 on thread ForkJoinPool.commonPool-worker-1",
            "3 on thread ForkJoinPool.commonPool-worker-1"
        )
    }

    @Test
    fun testGuideReactiveContextExample03() {
        test { guide.reactive.context.example03.main(emptyArray()) }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testGuideReactiveContextExample04() {
        test { guide.reactive.context.example04.main(emptyArray()) }.verifyLinesStart(
            "1 on thread main",
            "2 on thread main",
            "3 on thread main"
        )
    }

    @Test
    fun testGuideReactiveContextExample05() {
        test { guide.reactive.context.example05.main(emptyArray()) }.verifyLinesStart(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }
}
