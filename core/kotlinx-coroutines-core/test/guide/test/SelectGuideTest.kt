// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class SelectGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideSelect01() {
        test("KotlinxCoroutinesGuideSelect01") { kotlinx.coroutines.guide.select01.main() }.verifyLines(
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
    fun testKotlinxCoroutinesGuideSelect02() {
        test("KotlinxCoroutinesGuideSelect02") { kotlinx.coroutines.guide.select02.main() }.verifyLines(
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
    fun testKotlinxCoroutinesGuideSelect03() {
        test("KotlinxCoroutinesGuideSelect03") { kotlinx.coroutines.guide.select03.main() }.verifyLines(
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
    fun testKotlinxCoroutinesGuideSelect04() {
        test("KotlinxCoroutinesGuideSelect04") { kotlinx.coroutines.guide.select04.main() }.verifyLines(
            "Deferred 4 produced answer 'Waited for 128 ms'",
            "11 coroutines are still active"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSelect05() {
        test("KotlinxCoroutinesGuideSelect05") { kotlinx.coroutines.guide.select05.main() }.verifyLines(
            "BEGIN",
            "Replace",
            "END",
            "Channel was closed"
        )
    }
}
