/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from exception-handling.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import kotlinx.coroutines.knit.*
import org.junit.Test

class ExceptionsGuideTest {
    @Test
    fun testExampleExceptions01() {
        test("ExampleExceptions01") { kotlinx.coroutines.guide.exampleExceptions01.main() }.verifyExceptions(
            "Throwing exception from launch",
            "Exception in thread \"DefaultDispatcher-worker-2 @coroutine#2\" java.lang.IndexOutOfBoundsException",
            "Joined failed job",
            "Throwing exception from async",
            "Caught ArithmeticException"
        )
    }

    @Test
    fun testExampleExceptions02() {
        test("ExampleExceptions02") { kotlinx.coroutines.guide.exampleExceptions02.main() }.verifyLines(
            "CoroutineExceptionHandler got java.lang.AssertionError"
        )
    }

    @Test
    fun testExampleExceptions03() {
        test("ExampleExceptions03") { kotlinx.coroutines.guide.exampleExceptions03.main() }.verifyLines(
            "Cancelling child",
            "Child is cancelled",
            "Parent is not cancelled"
        )
    }

    @Test
    fun testExampleExceptions04() {
        test("ExampleExceptions04") { kotlinx.coroutines.guide.exampleExceptions04.main() }.verifyLines(
            "Second child throws an exception",
            "Children are cancelled, but exception is not handled until all children terminate",
            "The first child finished its non cancellable block",
            "CoroutineExceptionHandler got java.lang.ArithmeticException"
        )
    }

    @Test
    fun testExampleExceptions05() {
        test("ExampleExceptions05") { kotlinx.coroutines.guide.exampleExceptions05.main() }.verifyLines(
            "CoroutineExceptionHandler got java.io.IOException with suppressed [java.lang.ArithmeticException]"
        )
    }

    @Test
    fun testExampleExceptions06() {
        test("ExampleExceptions06") { kotlinx.coroutines.guide.exampleExceptions06.main() }.verifyLines(
            "Rethrowing CancellationException with original cause",
            "CoroutineExceptionHandler got java.io.IOException"
        )
    }

    @Test
    fun testExampleSupervision01() {
        test("ExampleSupervision01") { kotlinx.coroutines.guide.exampleSupervision01.main() }.verifyLines(
            "The first child is failing",
            "The first child is cancelled: true, but the second one is still active",
            "Cancelling the supervisor",
            "The second child is cancelled because the supervisor was cancelled"
        )
    }

    @Test
    fun testExampleSupervision02() {
        test("ExampleSupervision02") { kotlinx.coroutines.guide.exampleSupervision02.main() }.verifyLines(
            "The child is sleeping",
            "Throwing an exception from the scope",
            "The child is cancelled",
            "Caught an assertion error"
        )
    }

    @Test
    fun testExampleSupervision03() {
        test("ExampleSupervision03") { kotlinx.coroutines.guide.exampleSupervision03.main() }.verifyLines(
            "The scope is completing",
            "The child throws an exception",
            "CoroutineExceptionHandler got java.lang.AssertionError",
            "The scope is completed"
        )
    }
}
