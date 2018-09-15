// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class ComposingGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose01() {
        test("KotlinxCoroutinesExperimentalGuideCompose01") { kotlinx.coroutines.experimental.guide.compose01.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 2017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose02() {
        test("KotlinxCoroutinesExperimentalGuideCompose02") { kotlinx.coroutines.experimental.guide.compose02.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose03() {
        test("KotlinxCoroutinesExperimentalGuideCompose03") { kotlinx.coroutines.experimental.guide.compose03.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose04() {
        test("KotlinxCoroutinesExperimentalGuideCompose04") { kotlinx.coroutines.experimental.guide.compose04.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1085 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose05() {
        test("KotlinxCoroutinesExperimentalGuideCompose05") { kotlinx.coroutines.experimental.guide.compose05.main(emptyArray()) }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCompose06() {
        test("KotlinxCoroutinesExperimentalGuideCompose06") { kotlinx.coroutines.experimental.guide.compose06.main(emptyArray()) }.verifyLines(
            "Second child throws an exception",
            "First child was cancelled",
            "Computation failed with ArithmeticException"
        )
    }
}
