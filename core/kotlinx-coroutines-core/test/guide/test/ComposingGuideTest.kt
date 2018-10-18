// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class ComposingGuideTest {

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
}
