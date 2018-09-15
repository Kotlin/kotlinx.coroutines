// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class SelectGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect01() {
        test("KotlinxCoroutinesExperimentalGuideSelect01") { kotlinx.coroutines.experimental.guide.select01.main(emptyArray()) }.verifyLines(
            "fizz -> 'Fizz'",
            "buzz -> 'Buzz!'",
            "fizz -> 'Fizz'",
            "fizz -> 'Fizz'",
            "buzz -> 'Buzz!'",
            "fizz -> 'Fizz'",
            "buzz -> 'Buzz!'"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect02() {
        test("KotlinxCoroutinesExperimentalGuideSelect02") { kotlinx.coroutines.experimental.guide.select02.main(emptyArray()) }.verifyLines(
            "a -> 'Hello 0'",
            "a -> 'Hello 1'",
            "b -> 'World 0'",
            "a -> 'Hello 2'",
            "a -> 'Hello 3'",
            "b -> 'World 1'",
            "Channel 'a' is closed",
            "Channel 'a' is closed"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect03() {
        test("KotlinxCoroutinesExperimentalGuideSelect03") { kotlinx.coroutines.experimental.guide.select03.main(emptyArray()) }.verifyLines(
            "Consuming 1",
            "Side channel has 2",
            "Side channel has 3",
            "Consuming 4",
            "Side channel has 5",
            "Side channel has 6",
            "Consuming 7",
            "Side channel has 8",
            "Side channel has 9",
            "Consuming 10",
            "Done consuming"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect04() {
        test("KotlinxCoroutinesExperimentalGuideSelect04") { kotlinx.coroutines.experimental.guide.select04.main(emptyArray()) }.verifyLines(
            "Deferred 4 produced answer 'Waited for 128 ms'",
            "11 coroutines are still active"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideSelect05() {
        test("KotlinxCoroutinesExperimentalGuideSelect05") { kotlinx.coroutines.experimental.guide.select05.main(emptyArray()) }.verifyLines(
            "BEGIN",
            "Replace",
            "END",
            "Channel was closed"
        )
    }
}
