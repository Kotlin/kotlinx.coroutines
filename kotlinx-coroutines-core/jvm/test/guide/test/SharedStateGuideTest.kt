/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from shared-mutable-state-and-concurrency.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class SharedStateGuideTest {
    @Test
    fun testExampleSync01() {
        test("ExampleSync01") { kotlinx.coroutines.guide.exampleSync01.main() }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testExampleSync02() {
        test("ExampleSync02") { kotlinx.coroutines.guide.exampleSync02.main() }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testExampleSync03() {
        test("ExampleSync03") { kotlinx.coroutines.guide.exampleSync03.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testExampleSync04() {
        test("ExampleSync04") { kotlinx.coroutines.guide.exampleSync04.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testExampleSync05() {
        test("ExampleSync05") { kotlinx.coroutines.guide.exampleSync05.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testExampleSync06() {
        test("ExampleSync06") { kotlinx.coroutines.guide.exampleSync06.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testExampleSync07() {
        test("ExampleSync07") { kotlinx.coroutines.guide.exampleSync07.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }
}
