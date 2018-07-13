// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class CancellationTimeOutsGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideCancel01() {
        test("KotlinxCoroutinesGuideCancel01") { kotlinx.coroutines.guide.cancel01.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel02() {
        test("KotlinxCoroutinesGuideCancel02") { kotlinx.coroutines.guide.cancel02.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm sleeping 3 ...",
            "I'm sleeping 4 ...",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel03() {
        test("KotlinxCoroutinesGuideCancel03") { kotlinx.coroutines.guide.cancel03.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel04() {
        test("KotlinxCoroutinesGuideCancel04") { kotlinx.coroutines.guide.cancel04.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm running finally",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel05() {
        test("KotlinxCoroutinesGuideCancel05") { kotlinx.coroutines.guide.cancel05.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm running finally",
            "And I've just delayed for 1 sec because I'm non-cancellable",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel06() {
        test("KotlinxCoroutinesGuideCancel06") { kotlinx.coroutines.guide.cancel06.main(emptyArray()) }.verifyLinesStartWith(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Exception in thread \"main\" kotlinx.coroutines.TimeoutCancellationException: Timed out waiting for 1300 ms"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideCancel07() {
        test("KotlinxCoroutinesGuideCancel07") { kotlinx.coroutines.guide.cancel07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Result is null"
        )
    }
}
