/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from select-expression.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class SelectGuideTest {
    @Test
    fun testExampleSelect01() {
        test("ExampleSelect01") { kotlinx.coroutines.guide.exampleSelect01.main() }.verifyLines(
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
    fun testExampleSelect02() {
        test("ExampleSelect02") { kotlinx.coroutines.guide.exampleSelect02.main() }.verifyLines(
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
    fun testExampleSelect03() {
        test("ExampleSelect03") { kotlinx.coroutines.guide.exampleSelect03.main() }.verifyLines(
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
    fun testExampleSelect04() {
        test("ExampleSelect04") { kotlinx.coroutines.guide.exampleSelect04.main() }.verifyLines(
            "Deferred 4 produced answer 'Waited for 128 ms'",
            "11 coroutines are still active"
        )
    }

    @Test
    fun testExampleSelect05() {
        test("ExampleSelect05") { kotlinx.coroutines.guide.exampleSelect05.main() }.verifyLines(
            "BEGIN",
            "Replace",
            "END",
            "Channel was closed"
        )
    }
}
