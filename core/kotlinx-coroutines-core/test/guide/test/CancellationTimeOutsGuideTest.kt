// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class CancellationTimeOutsGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel01() {
        test("KotlinxCoroutinesExperimentalGuideCancel01") { kotlinx.coroutines.experimental.guide.cancel01.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel02() {
        test("KotlinxCoroutinesExperimentalGuideCancel02") { kotlinx.coroutines.experimental.guide.cancel02.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesExperimentalGuideCancel03() {
        test("KotlinxCoroutinesExperimentalGuideCancel03") { kotlinx.coroutines.experimental.guide.cancel03.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel04() {
        test("KotlinxCoroutinesExperimentalGuideCancel04") { kotlinx.coroutines.experimental.guide.cancel04.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "main: I'm tired of waiting!",
            "I'm running finally",
            "main: Now I can quit."
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel05() {
        test("KotlinxCoroutinesExperimentalGuideCancel05") { kotlinx.coroutines.experimental.guide.cancel05.main(emptyArray()) }.verifyLines(
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
    fun testKotlinxCoroutinesExperimentalGuideCancel06() {
        test("KotlinxCoroutinesExperimentalGuideCancel06") { kotlinx.coroutines.experimental.guide.cancel06.main(emptyArray()) }.verifyLinesStartWith(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Exception in thread \"main\" kotlinx.coroutines.experimental.TimeoutCancellationException: Timed out waiting for 1300 MILLISECONDS"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideCancel07() {
        test("KotlinxCoroutinesExperimentalGuideCancel07") { kotlinx.coroutines.experimental.guide.cancel07.main(emptyArray()) }.verifyLines(
            "I'm sleeping 0 ...",
            "I'm sleeping 1 ...",
            "I'm sleeping 2 ...",
            "Result is null"
        )
    }
}
