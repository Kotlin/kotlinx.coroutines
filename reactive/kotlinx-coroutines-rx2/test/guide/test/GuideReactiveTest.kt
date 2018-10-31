// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package kotlinx.coroutines.rx2.guide.test

import kotlinx.coroutines.guide.test.*
import org.junit.Test

class GuideReactiveTest : ReactiveTestBase() {

    @Test
    fun testKotlinxCoroutinesRx2GuideBasic01() {
        test("KotlinxCoroutinesRx2GuideBasic01") { kotlinx.coroutines.rx2.guide.basic01.main() }.verifyLines(
            "Elements:",
            "Begin",
            "1",
            "2",
            "3",
            "Again:"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideBasic02() {
        test("KotlinxCoroutinesRx2GuideBasic02") { kotlinx.coroutines.rx2.guide.basic02.main() }.verifyLines(
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
    fun testKotlinxCoroutinesRx2GuideBasic03() {
        test("KotlinxCoroutinesRx2GuideBasic03") { kotlinx.coroutines.rx2.guide.basic03.main() }.verifyLines(
            "OnSubscribe",
            "1",
            "2",
            "3",
            "Finally"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideBasic04() {
        test("KotlinxCoroutinesRx2GuideBasic04") { kotlinx.coroutines.rx2.guide.basic04.main() }.verifyLines(
            "OnSubscribe",
            "1",
            "2",
            "3",
            "4",
            "OnComplete",
            "Finally",
            "5"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideBasic05() {
        test("KotlinxCoroutinesRx2GuideBasic05") { kotlinx.coroutines.rx2.guide.basic05.main() }.verifyLines(
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
    fun testKotlinxCoroutinesRx2GuideBasic06() {
        test("KotlinxCoroutinesRx2GuideBasic06") { kotlinx.coroutines.rx2.guide.basic06.main() }.verifyLines(
            "two",
            "three",
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideBasic07() {
        test("KotlinxCoroutinesRx2GuideBasic07") { kotlinx.coroutines.rx2.guide.basic07.main() }.verifyLines(
            "two",
            "three",
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideBasic08() {
        test("KotlinxCoroutinesRx2GuideBasic08") { kotlinx.coroutines.rx2.guide.basic08.main() }.verifyLines(
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideBasic09() {
        test("KotlinxCoroutinesRx2GuideBasic09") { kotlinx.coroutines.rx2.guide.basic09.main() }.verifyLines(
            "four"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideOperators01() {
        test("KotlinxCoroutinesRx2GuideOperators01") { kotlinx.coroutines.rx2.guide.operators01.main() }.verifyLines(
            "1",
            "2",
            "3",
            "4",
            "5"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideOperators02() {
        test("KotlinxCoroutinesRx2GuideOperators02") { kotlinx.coroutines.rx2.guide.operators02.main() }.verifyLines(
            "2 is even",
            "4 is even"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideOperators03() {
        test("KotlinxCoroutinesRx2GuideOperators03") { kotlinx.coroutines.rx2.guide.operators03.main() }.verifyLines(
            "1",
            "2"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideOperators04() {
        test("KotlinxCoroutinesRx2GuideOperators04") { kotlinx.coroutines.rx2.guide.operators04.main() }.verifyLines(
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
    fun testKotlinxCoroutinesRx2GuideContext01() {
        test("KotlinxCoroutinesRx2GuideContext01") { kotlinx.coroutines.rx2.guide.context01.main() }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideContext02() {
        test("KotlinxCoroutinesRx2GuideContext02") { kotlinx.coroutines.rx2.guide.context02.main() }.verifyLinesStart(
            "1 on thread ForkJoinPool.commonPool-worker-1",
            "2 on thread ForkJoinPool.commonPool-worker-1",
            "3 on thread ForkJoinPool.commonPool-worker-1"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideContext03() {
        test("KotlinxCoroutinesRx2GuideContext03") { kotlinx.coroutines.rx2.guide.context03.main() }.verifyLinesFlexibleThread(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideContext04() {
        test("KotlinxCoroutinesRx2GuideContext04") { kotlinx.coroutines.rx2.guide.context04.main() }.verifyLinesStart(
            "1 on thread main",
            "2 on thread main",
            "3 on thread main"
        )
    }

    @Test
    fun testKotlinxCoroutinesRx2GuideContext05() {
        test("KotlinxCoroutinesRx2GuideContext05") { kotlinx.coroutines.rx2.guide.context05.main() }.verifyLinesStart(
            "1 on thread RxComputationThreadPool-1",
            "2 on thread RxComputationThreadPool-1",
            "3 on thread RxComputationThreadPool-1"
        )
    }
}
