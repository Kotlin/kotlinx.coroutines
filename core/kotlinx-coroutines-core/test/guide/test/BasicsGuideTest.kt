// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class BasicsGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideBasic01() {
        test("KotlinxCoroutinesGuideBasic01") { kotlinx.coroutines.guide.basic01.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic02() {
        test("KotlinxCoroutinesGuideBasic02") { kotlinx.coroutines.guide.basic02.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic02b() {
        test("KotlinxCoroutinesGuideBasic02b") { kotlinx.coroutines.guide.basic02b.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic03() {
        test("KotlinxCoroutinesGuideBasic03") { kotlinx.coroutines.guide.basic03.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic03s() {
        test("KotlinxCoroutinesGuideBasic03s") { kotlinx.coroutines.guide.basic03s.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic04() {
        test("KotlinxCoroutinesGuideBasic04") { kotlinx.coroutines.guide.basic04.main(emptyArray()) }.verifyLines(
            "Task from coroutine scope",
            "Task from runBlocking",
            "Task from nested launch",
            "Coroutine scope is over"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic05() {
        test("KotlinxCoroutinesGuideBasic05") { kotlinx.coroutines.guide.basic05.main(emptyArray()) }.verifyLines(
            "Hello,",
            "World!"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic06() {
        test("KotlinxCoroutinesGuideBasic06") { kotlinx.coroutines.guide.basic06.main(emptyArray()) }.also { lines ->
            check(lines.size == 1 && lines[0] == ".".repeat(100_000))
        }
    }

    @Test
    fun testKotlinxCoroutinesGuideBasic07() {
        test("KotlinxCoroutinesGuideBasic07") { kotlinx.coroutines.guide.basic07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ..."
        )
    }
}
