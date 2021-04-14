/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from channels.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class ChannelsGuideTest {
    @Test
    fun testExampleChannel01() {
        test("ExampleChannel01") { kotlinx.coroutines.guide.exampleChannel01.main() }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testExampleChannel02() {
        test("ExampleChannel02") { kotlinx.coroutines.guide.exampleChannel02.main() }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testExampleChannel03() {
        test("ExampleChannel03") { kotlinx.coroutines.guide.exampleChannel03.main() }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testExampleChannel04() {
        test("ExampleChannel04") { kotlinx.coroutines.guide.exampleChannel04.main() }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testExampleChannel05() {
        test("ExampleChannel05") { kotlinx.coroutines.guide.exampleChannel05.main() }.verifyLines(
            "2",
            "3",
            "5",
            "7",
            "11",
            "13",
            "17",
            "19",
            "23",
            "29"
        )
    }

    @Test
    fun testExampleChannel06() {
        test("ExampleChannel06") { kotlinx.coroutines.guide.exampleChannel06.main() }.also { lines ->
            check(lines.size == 10 && lines.withIndex().all { (i, line) -> line.startsWith("Processor #") && line.endsWith(" received ${i + 1}") })
        }
    }

    @Test
    fun testExampleChannel07() {
        test("ExampleChannel07") { kotlinx.coroutines.guide.exampleChannel07.main() }.verifyLines(
            "foo",
            "foo",
            "BAR!",
            "foo",
            "foo",
            "BAR!"
        )
    }

    @Test
    fun testExampleChannel08() {
        test("ExampleChannel08") { kotlinx.coroutines.guide.exampleChannel08.main() }.verifyLines(
            "Sending 0",
            "Sending 1",
            "Sending 2",
            "Sending 3",
            "Sending 4"
        )
    }

    @Test
    fun testExampleChannel09() {
        test("ExampleChannel09") { kotlinx.coroutines.guide.exampleChannel09.main() }.verifyLines(
            "ping Ball(hits=1)",
            "pong Ball(hits=2)",
            "ping Ball(hits=3)",
            "pong Ball(hits=4)"
        )
    }

    @Test
    fun testExampleChannel10() {
        test("ExampleChannel10") { kotlinx.coroutines.guide.exampleChannel10.main() }.verifyLines(
            "Initial element is available immediately: kotlin.Unit",
            "Next element is not ready in 50 ms: null",
            "Next element is ready in 100 ms: kotlin.Unit",
            "Consumer pauses for 150ms",
            "Next element is available immediately after large consumer delay: kotlin.Unit",
            "Next element is ready in 50ms after consumer pause in 150ms: kotlin.Unit"
        )
    }
}
