// This file was automatically generated from Delay.kt by Knit tool. Do not edit.
package kotlinx.coroutines.examples.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class FlowDelayTest {
    @Test
    fun testExampleDelay01() {
        test("ExampleDelay01") { kotlinx.coroutines.examples.exampleDelay01.main() }.verifyLines(
            "3, 4, 5"
        )
    }

    @Test
    fun testExampleDelay02() {
        test("ExampleDelay02") { kotlinx.coroutines.examples.exampleDelay02.main() }.verifyLines(
            "1, 3, 4, 5"
        )
    }

    @Test
    fun testExampleDelayDuration01() {
        test("ExampleDelayDuration01") { kotlinx.coroutines.examples.exampleDelayDuration01.main() }.verifyLines(
            "3, 4, 5"
        )
    }

    @Test
    fun testExampleDelayDuration02() {
        test("ExampleDelayDuration02") { kotlinx.coroutines.examples.exampleDelayDuration02.main() }.verifyLines(
            "1, 3, 4, 5"
        )
    }

    @Test
    fun testExampleDelay03() {
        test("ExampleDelay03") { kotlinx.coroutines.examples.exampleDelay03.main() }.verifyLines(
            "1, 3, 5, 7, 9"
        )
    }

    @Test
    fun testExampleDelayDuration03() {
        test("ExampleDelayDuration03") { kotlinx.coroutines.examples.exampleDelayDuration03.main() }.verifyLines(
            "1, 3, 5, 7, 9"
        )
    }

    @Test
    fun testExampleTimeoutDuration01() {
        test("ExampleTimeoutDuration01") { kotlinx.coroutines.examples.exampleTimeoutDuration01.main() }.verifyLines(
            "1, 2, 3, -1"
        )
    }
}
