// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.rx2.guide.test

import kotlinx.coroutines.experimental.guide.test.*
import org.junit.Test

class GuideReactiveTest : ReactiveTestBase() {

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic01() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic01") { kotlinx.coroutines.experimental.rx2.guide.basic01.main(emptyArray()) }.verifyLines(
            "Elements:",
            "Begin",
            "1",
            "2",
            "3",
            "Again:"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic02() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic02") { kotlinx.coroutines.experimental.rx2.guide.basic02.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic03() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic03") { kotlinx.coroutines.experimental.rx2.guide.basic03.main(emptyArray()) }.verifyLines(
            "OnSubscribe",
            "1",
            "2",
            "3",
            "Finally"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic04() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic04") { kotlinx.coroutines.experimental.rx2.guide.basic04.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic05() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic05") { kotlinx.coroutines.experimental.rx2.guide.basic05.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic06() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic06") { kotlinx.coroutines.experimental.rx2.guide.basic06.main(emptyArray()) }.verifyLines(
            "two",
            "three",
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic07() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic07") { kotlinx.coroutines.experimental.rx2.guide.basic07.main(emptyArray()) }.verifyLines(
            "two",
            "three",
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic08() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic08") { kotlinx.coroutines.experimental.rx2.guide.basic08.main(emptyArray()) }.verifyLines(
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideBasic09() {
        test("KotlinxCoroutinesExperimentalRx2GuideBasic09") { kotlinx.coroutines.experimental.rx2.guide.basic09.main(emptyArray()) }.verifyLines(
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideOperators01() {
        test("KotlinxCoroutinesExperimentalRx2GuideOperators01") { kotlinx.coroutines.experimental.rx2.guide.operators01.main(emptyArray()) }.verifyLines(
            "1",
            "2",
            "3",
            "4",
            "5"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideOperators02() {
        test("KotlinxCoroutinesExperimentalRx2GuideOperators02") { kotlinx.coroutines.experimental.rx2.guide.operators02.main(emptyArray()) }.verifyLines(
            "2 is even",
            "4 is even"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideOperators03() {
        test("KotlinxCoroutinesExperimentalRx2GuideOperators03") { kotlinx.coroutines.experimental.rx2.guide.operators03.main(emptyArray()) }.verifyLines(
            "1",
            "2"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideOperators04() {
        test("KotlinxCoroutinesExperimentalRx2GuideOperators04") { kotlinx.coroutines.experimental.rx2.guide.operators04.main(emptyArray()) }.verifyLines(
            "1",
            "2",
            "11",
            "3",
            "4",
            "12",
            "13"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideContext01() {
        test("KotlinxCoroutinesExperimentalRx2GuideContext01") { kotlinx.coroutines.experimental.rx2.guide.context01.main(emptyArray()) }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideContext02() {
        test("KotlinxCoroutinesExperimentalRx2GuideContext02") { kotlinx.coroutines.experimental.rx2.guide.context02.main(emptyArray()) }.verifyLinesStart(
            "1 on thread ForkJoinPool.commonPool-worker-1",
            "2 on thread ForkJoinPool.commonPool-worker-1",
            "3 on thread ForkJoinPool.commonPool-worker-1"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideContext03() {
        test("KotlinxCoroutinesExperimentalRx2GuideContext03") { kotlinx.coroutines.experimental.rx2.guide.context03.main(emptyArray()) }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideContext04() {
        test("KotlinxCoroutinesExperimentalRx2GuideContext04") { kotlinx.coroutines.experimental.rx2.guide.context04.main(emptyArray()) }.verifyLinesStart(
            "1 on thread main",
            "2 on thread main",
            "3 on thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalRx2GuideContext05() {
        test("KotlinxCoroutinesExperimentalRx2GuideContext05") { kotlinx.coroutines.experimental.rx2.guide.context05.main(emptyArray()) }.verifyLinesStart(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }
}
