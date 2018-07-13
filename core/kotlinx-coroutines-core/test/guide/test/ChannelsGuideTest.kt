// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class ChannelsGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideChannel01() {
        test("KotlinxCoroutinesGuideChannel01") { kotlinx.coroutines.guide.channel01.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel02() {
        test("KotlinxCoroutinesGuideChannel02") { kotlinx.coroutines.guide.channel02.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel03() {
        test("KotlinxCoroutinesGuideChannel03") { kotlinx.coroutines.guide.channel03.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel04() {
        test("KotlinxCoroutinesGuideChannel04") { kotlinx.coroutines.guide.channel04.main(emptyArray()) }.verifyLines(
            "1",
            "4",
            "9",
            "16",
            "25",
            "Done!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel05() {
        test("KotlinxCoroutinesGuideChannel05") { kotlinx.coroutines.guide.channel05.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesGuideChannel06() {
        test("KotlinxCoroutinesGuideChannel06") { kotlinx.coroutines.guide.channel06.main(emptyArray()) }.also { lines ->
            check(lines.size == 10 && lines.withIndex().all { (i, line) -> line.startsWith("Processor #") && line.endsWith(" received ${i + 1}") })
        }
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel07() {
        test("KotlinxCoroutinesGuideChannel07") { kotlinx.coroutines.guide.channel07.main(emptyArray()) }.verifyLines(
            "foo",
            "foo",
            "BAR!",
            "foo",
            "foo",
            "BAR!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel08() {
        test("KotlinxCoroutinesGuideChannel08") { kotlinx.coroutines.guide.channel08.main(emptyArray()) }.verifyLines(
            "Sending 0",
            "Sending 1",
            "Sending 2",
            "Sending 3",
            "Sending 4"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel09() {
        test("KotlinxCoroutinesGuideChannel09") { kotlinx.coroutines.guide.channel09.main(emptyArray()) }.verifyLines(
            "ping Ball(hits=1)",
            "pong Ball(hits=2)",
            "ping Ball(hits=3)",
            "pong Ball(hits=4)"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideChannel10() {
        test("KotlinxCoroutinesGuideChannel10") { kotlinx.coroutines.guide.channel10.main(emptyArray()) }.verifyLines(
            "Initial element is available immediately: kotlin.Unit",
            "Next element is not ready in 50 ms: null",
            "Next element is ready in 100 ms: kotlin.Unit",
            "Consumer pauses for 150ms",
            "Next element is available immediately after large consumer delay: kotlin.Unit",
            "Next element is ready in 50ms after consumer pause in 150ms: kotlin.Unit"
        )
    }
}
