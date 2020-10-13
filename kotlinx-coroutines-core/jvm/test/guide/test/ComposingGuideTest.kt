/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from composing-suspending-functions.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class ComposingGuideTest {
    @Test
    fun testExampleCompose01() {
        test("ExampleCompose01") { kotlinx.coroutines.guide.exampleCompose01.main() }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 2017 ms"
        )
    }

    @Test
    fun testExampleCompose02() {
        test("ExampleCompose02") { kotlinx.coroutines.guide.exampleCompose02.main() }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testExampleCompose03() {
        test("ExampleCompose03") { kotlinx.coroutines.guide.exampleCompose03.main() }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testExampleCompose04() {
        test("ExampleCompose04") { kotlinx.coroutines.guide.exampleCompose04.main() }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1085 ms"
        )
    }

    @Test
    fun testExampleCompose05() {
        test("ExampleCompose05") { kotlinx.coroutines.guide.exampleCompose05.main() }.verifyLinesArbitraryTime(
            "The answer is 42",
            "Completed in 1017 ms"
        )
    }

    @Test
    fun testExampleCompose06() {
        test("ExampleCompose06") { kotlinx.coroutines.guide.exampleCompose06.main() }.verifyLines(
            "Second child throws an exception",
            "First child was cancelled",
            "Computation failed with ArithmeticException"
        )
    }
}
