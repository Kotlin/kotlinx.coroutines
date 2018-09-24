// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class ExceptionsGuideTest {

    @Test
    fun testKotlinxCoroutinesExperimentalGuideExceptions01() {
        test("KotlinxCoroutinesExperimentalGuideExceptions01") { kotlinx.coroutines.experimental.guide.exceptions01.main(emptyArray()) }.verifyExceptions(
            "Throwing exception from launch",
            "Exception in thread \"ForkJoinPool.commonPool-worker-2 @coroutine#2\" java.lang.IndexOutOfBoundsException",
            "Joined failed job",
            "Throwing exception from async",
            "Caught ArithmeticException"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideExceptions02() {
        test("KotlinxCoroutinesExperimentalGuideExceptions02") { kotlinx.coroutines.experimental.guide.exceptions02.main(emptyArray()) }.verifyLines(
            "Caught java.lang.AssertionError"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideExceptions03() {
        test("KotlinxCoroutinesExperimentalGuideExceptions03") { kotlinx.coroutines.experimental.guide.exceptions03.main(emptyArray()) }.verifyLines(
            "Cancelling child",
            "Child is cancelled",
            "Parent is not cancelled"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideExceptions04() {
        test("KotlinxCoroutinesExperimentalGuideExceptions04") { kotlinx.coroutines.experimental.guide.exceptions04.main(emptyArray()) }.verifyLines(
            "Second child throws an exception",
            "Children are cancelled, but exception is not handled until all children terminate",
            "The first child finished its non cancellable block",
            "Caught java.lang.ArithmeticException"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideExceptions05() {
        test("KotlinxCoroutinesExperimentalGuideExceptions05") { kotlinx.coroutines.experimental.guide.exceptions05.main(emptyArray()) }.verifyLines(
            "Caught java.io.IOException with suppressed [java.lang.ArithmeticException]"
        )
    }

    @Test
    fun testKotlinxCoroutinesExperimentalGuideExceptions06() {
        test("KotlinxCoroutinesExperimentalGuideExceptions06") { kotlinx.coroutines.experimental.guide.exceptions06.main(emptyArray()) }.verifyLines(
            "Rethrowing CancellationException with original cause",
            "Caught original java.io.IOException"
        )
    }
}
