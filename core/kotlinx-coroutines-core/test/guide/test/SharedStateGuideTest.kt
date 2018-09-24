// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class SharedStateGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync01() {
        test("KotlinxCoroutinesExperimentalGuideSync01") { kotlinx.coroutines.experimental.guide.sync01.main(emptyArray()) }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync01b() {
        test("KotlinxCoroutinesExperimentalGuideSync01b") { kotlinx.coroutines.experimental.guide.sync01b.main(emptyArray()) }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync02() {
        test("KotlinxCoroutinesExperimentalGuideSync02") { kotlinx.coroutines.experimental.guide.sync02.main(emptyArray()) }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync03() {
        test("KotlinxCoroutinesExperimentalGuideSync03") { kotlinx.coroutines.experimental.guide.sync03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync04() {
        test("KotlinxCoroutinesExperimentalGuideSync04") { kotlinx.coroutines.experimental.guide.sync04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync05() {
        test("KotlinxCoroutinesExperimentalGuideSync05") { kotlinx.coroutines.experimental.guide.sync05.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync06() {
        test("KotlinxCoroutinesExperimentalGuideSync06") { kotlinx.coroutines.experimental.guide.sync06.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSync07() {
        test("KotlinxCoroutinesExperimentalGuideSync07") { kotlinx.coroutines.experimental.guide.sync07.main(emptyArray()) }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }
}
