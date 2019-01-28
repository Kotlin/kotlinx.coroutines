// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class SharedStateGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideSync01() {
        test("KotlinxCoroutinesGuideSync01") { kotlinx.coroutines.guide.sync01.main() }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync01b() {
        test("KotlinxCoroutinesGuideSync01b") { kotlinx.coroutines.guide.sync01b.main() }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync02() {
        test("KotlinxCoroutinesGuideSync02") { kotlinx.coroutines.guide.sync02.main() }.verifyLinesStart(
            "Completed 100000 actions in",
            "Counter ="
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync03() {
        test("KotlinxCoroutinesGuideSync03") { kotlinx.coroutines.guide.sync03.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync04() {
        test("KotlinxCoroutinesGuideSync04") { kotlinx.coroutines.guide.sync04.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync05() {
        test("KotlinxCoroutinesGuideSync05") { kotlinx.coroutines.guide.sync05.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync06() {
        test("KotlinxCoroutinesGuideSync06") { kotlinx.coroutines.guide.sync06.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSync07() {
        test("KotlinxCoroutinesGuideSync07") { kotlinx.coroutines.guide.sync07.main() }.verifyLinesArbitraryTime(
            "Completed 100000 actions in xxx ms",
            "Counter = 100000"
        )
    }
}
