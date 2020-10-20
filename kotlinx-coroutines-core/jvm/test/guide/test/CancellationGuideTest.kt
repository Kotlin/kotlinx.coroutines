/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from cancellation-and-timeouts.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class CancellationGuideTest {
    @Test
    fun testExampleCancel01() {
        test("ExampleCancel01") { kotlinx.coroutines.guide.exampleCancel01.main() }.verifyLines(
            "job: I'm sleeping 0 ...",
            "job: I'm sleeping 1 ...",
            "job: I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testExampleCancel02() {
        test("ExampleCancel02") { kotlinx.coroutines.guide.exampleCancel02.main() }.verifyLines(
            "job: I'm sleeping 0 ...",
            "job: I'm sleeping 1 ...",
            "job: I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "job: I'm sleeping 3 ...",
            "job: I'm sleeping 4 ...",
            "main: Now I can quit."
        )
    }

    @Test
    fun testExampleCancel03() {
        test("ExampleCancel03") { kotlinx.coroutines.guide.exampleCancel03.main() }.verifyLines(
            "job: I'm sleeping 0 ...",
            "job: I'm sleeping 1 ...",
            "job: I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testExampleCancel04() {
        test("ExampleCancel04") { kotlinx.coroutines.guide.exampleCancel04.main() }.verifyLines(
            "job: I'm sleeping 0 ...",
            "job: I'm sleeping 1 ...",
            "job: I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "job: I'm running finally",
            "main: Now I can quit."
        )
    }

    @Test
    fun testExampleCancel05() {
        test("ExampleCancel05") { kotlinx.coroutines.guide.exampleCancel05.main() }.verifyLines(
            "job: I'm sleeping 0 ...",
            "job: I'm sleeping 1 ...",
            "job: I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "job: I'm running finally",
            "job: And I've just delayed for 1 sec because I'm non-cancellable",
            "main: Now I can quit."
        )
    }

    @Test
    fun testExampleCancel06() {
        test("ExampleCancel06") { kotlinx.coroutines.guide.exampleCancel06.main() }.verifyLinesStartWith(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Exception in thread \"main\" kotlinx.coroutines.TimeoutCancellationException: Timed out waiting for 1300 ms"
        )
    }

    @Test
    fun testExampleCancel07() {
        test("ExampleCancel07") { kotlinx.coroutines.guide.exampleCancel07.main() }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Result is null"
        )
    }

    @Test
    fun testExampleCancel09() {
        test("ExampleCancel09") { kotlinx.coroutines.guide.exampleCancel09.main() }.verifyLines(
            "0"
        )
    }
}
