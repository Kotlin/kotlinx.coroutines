/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-basics.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class BasicsGuideTest {
    @Test
    fun testExampleBasic01() {
        test("ExampleBasic01") { kotlinx.coroutines.guide.exampleBasic01.main() }.verifyLines(
            "Hello",
            "World!"
        )
    }

    @Test
    fun testExampleBasic02() {
        test("ExampleBasic02") { kotlinx.coroutines.guide.exampleBasic02.main() }.verifyLines(
            "Hello",
            "World!"
        )
    }

    @Test
    fun testExampleBasic03() {
        test("ExampleBasic03") { kotlinx.coroutines.guide.exampleBasic03.main() }.verifyLines(
            "Hello",
            "World!"
        )
    }

    @Test
    fun testExampleBasic04() {
        test("ExampleBasic04") { kotlinx.coroutines.guide.exampleBasic04.main() }.verifyLines(
            "Hello",
            "World 1",
            "World 2",
            "Done"
        )
    }

    @Test
    fun testExampleBasic05() {
        test("ExampleBasic05") { kotlinx.coroutines.guide.exampleBasic05.main() }.verifyLines(
            "Hello",
            "World!",
            "Done"
        )
    }

    @Test
    fun testExampleBasic06() {
        test("ExampleBasic06") { kotlinx.coroutines.guide.exampleBasic06.main() }.also { lines ->
            check(lines.size == 1 && lines[0] == ".".repeat(100_000))
        }
    }
}
