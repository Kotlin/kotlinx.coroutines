// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class ExceptionsGuideTest {

    @Test
    fun testKotlinxCoroutinesGuideExceptions01() {
        test("KotlinxCoroutinesGuideExceptions01") { kotlinx.coroutines.guide.exceptions01.main(emptyArray()) }.verifyExceptions(
            "Throwing exception from launch",
            "Exception in thread \"DefaultDispatcher-worker-2 @coroutine#2\" java.lang.IndexOutOfBoundsException",
            "Joined failed job",
            "Throwing exception from async",
            "Caught ArithmeticException"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions02() {
        test("KotlinxCoroutinesGuideExceptions02") { kotlinx.coroutines.guide.exceptions02.main(emptyArray()) }.verifyLines(
            "Caught java.lang.AssertionError"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions03() {
        test("KotlinxCoroutinesGuideExceptions03") { kotlinx.coroutines.guide.exceptions03.main(emptyArray()) }.verifyLines(
            "Cancelling child",
            "Child is cancelled",
            "Parent is not cancelled"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions04() {
        test("KotlinxCoroutinesGuideExceptions04") { kotlinx.coroutines.guide.exceptions04.main(emptyArray()) }.verifyLines(
            "Second child throws an exception",
            "Children are cancelled, but exception is not handled until all children terminate",
            "The first child finished its non cancellable block",
            "Caught java.lang.ArithmeticException"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions05() {
        test("KotlinxCoroutinesGuideExceptions05") { kotlinx.coroutines.guide.exceptions05.main(emptyArray()) }.verifyLines(
            "Caught java.io.IOException with suppressed [java.lang.ArithmeticException]"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideExceptions06() {
        test("KotlinxCoroutinesGuideExceptions06") { kotlinx.coroutines.guide.exceptions06.main(emptyArray()) }.verifyLines(
            "Rethrowing CancellationException with original cause",
            "Caught original java.io.IOException"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSupervision01() {
        test("KotlinxCoroutinesGuideSupervision01") { kotlinx.coroutines.guide.supervision01.main(emptyArray()) }.verifyLines(
            "First child is failing",
            "First child is cancelled: true, but second one is still active",
            "Cancelling supervisor",
            "Second child is cancelled because supervisor is cancelled"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSupervision02() {
        test("KotlinxCoroutinesGuideSupervision02") { kotlinx.coroutines.guide.supervision02.main(emptyArray()) }.verifyLines(
            "Child is sleeping",
            "Throwing exception from scope",
            "Child is cancelled",
            "Caught assertion error"
        )
    }

    @Test
    fun testKotlinxCoroutinesGuideSupervision03() {
        test("KotlinxCoroutinesGuideSupervision03") { kotlinx.coroutines.guide.supervision03.main(emptyArray()) }.verifyLines(
            "Scope is completing",
            "Child throws an exception",
            "Caught java.lang.AssertionError",
            "Scope is completed"
        )
    }
}
