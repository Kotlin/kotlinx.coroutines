// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class BasicsGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic01() {
        test("KotlinxCoroutinesExperimentalGuideBasic01") { kotlinx.coroutines.experimental.guide.basic01.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic02() {
        test("KotlinxCoroutinesExperimentalGuideBasic02") { kotlinx.coroutines.experimental.guide.basic02.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic02b() {
        test("KotlinxCoroutinesExperimentalGuideBasic02b") { kotlinx.coroutines.experimental.guide.basic02b.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic03() {
        test("KotlinxCoroutinesExperimentalGuideBasic03") { kotlinx.coroutines.experimental.guide.basic03.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic03s() {
        test("KotlinxCoroutinesExperimentalGuideBasic03s") { kotlinx.coroutines.experimental.guide.basic03s.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic04() {
        test("KotlinxCoroutinesExperimentalGuideBasic04") { kotlinx.coroutines.experimental.guide.basic04.main(emptyArray()) }.verifyLines(
            "Task from coroutine scope",
            "Task from runBlocking",
            "Task from nested launch",
            "Coroutine scope is over"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic05() {
        test("KotlinxCoroutinesExperimentalGuideBasic05") { kotlinx.coroutines.experimental.guide.basic05.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic06() {
        test("KotlinxCoroutinesExperimentalGuideBasic06") { kotlinx.coroutines.experimental.guide.basic06.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0] == ".".repeat(100_000))
        }
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideBasic07() {
        test("KotlinxCoroutinesExperimentalGuideBasic07") { kotlinx.coroutines.experimental.guide.basic07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ..."
        )
    }
}
