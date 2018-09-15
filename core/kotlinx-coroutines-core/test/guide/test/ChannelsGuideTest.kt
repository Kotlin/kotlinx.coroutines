// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class ChannelsGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel01() {
        test("KotlinxCoroutinesExperimentalGuideChannel01") { kotlinx.coroutines.experimental.guide.channel01.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel02() {
        test("KotlinxCoroutinesExperimentalGuideChannel02") { kotlinx.coroutines.experimental.guide.channel02.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel03() {
        test("KotlinxCoroutinesExperimentalGuideChannel03") { kotlinx.coroutines.experimental.guide.channel03.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel04() {
        test("KotlinxCoroutinesExperimentalGuideChannel04") { kotlinx.coroutines.experimental.guide.channel04.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel05() {
        test("KotlinxCoroutinesExperimentalGuideChannel05") { kotlinx.coroutines.experimental.guide.channel05.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesExperimentalGuideChannel06() {
        test("KotlinxCoroutinesExperimentalGuideChannel06") { kotlinx.coroutines.experimental.guide.channel06.main(emptyArray()) }.also { lines ->
            check(lines.size == 10 && lines.withIndex().all { (i, line) -> line.startsWith("Processor #") && line.endsWith(" received ${i + 1}") })
        }
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel07() {
        test("KotlinxCoroutinesExperimentalGuideChannel07") { kotlinx.coroutines.experimental.guide.channel07.main(emptyArray()) }.verifyLines(
            "foo",
            "foo",
            "BAR!",
            "foo",
            "foo",
            "BAR!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel08() {
        test("KotlinxCoroutinesExperimentalGuideChannel08") { kotlinx.coroutines.experimental.guide.channel08.main(emptyArray()) }.verifyLines(
            "Sending 0",
            "Sending 1",
            "Sending 2",
            "Sending 3",
            "Sending 4"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel09() {
        test("KotlinxCoroutinesExperimentalGuideChannel09") { kotlinx.coroutines.experimental.guide.channel09.main(emptyArray()) }.verifyLines(
            "ping Ball(hits=1)",
            "pong Ball(hits=2)",
            "ping Ball(hits=3)",
            "pong Ball(hits=4)"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideChannel10() {
        test("KotlinxCoroutinesExperimentalGuideChannel10") { kotlinx.coroutines.experimental.guide.channel10.main(emptyArray()) }.verifyLines(
            "Initial element is available immediately: kotlin.Unit",
            "Next element is not ready in 50 ms: null",
            "Next element is ready in 100 ms: kotlin.Unit",
            "Consumer pauses for 150ms",
            "Next element is available immediately after large consumer delay: kotlin.Unit",
            "Next element is ready in 50ms after consumer pause in 150ms: kotlin.Unit"
        )
    }
}
