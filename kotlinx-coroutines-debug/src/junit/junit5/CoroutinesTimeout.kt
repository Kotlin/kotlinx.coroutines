/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5
import kotlinx.coroutines.debug.*
import org.junit.jupiter.api.*
import org.junit.jupiter.api.extension.*
import org.junit.jupiter.api.parallel.*
import java.lang.annotation.*

/**
 * Coroutines timeout annotation that is similar to JUnit5's [Timeout] annotation. It allows running test methods in a
 * separate thread, failing them after the provided time limit and interrupting the thread.
 *
 * Additionally, it installs [DebugProbes] and dumps all coroutines at the moment of the timeout. It also cancels
 * coroutines on timeout if [cancelOnTimeout] set to `true`. The dump contains the coroutine creation stack traces.
 *
 * This annotation has an effect on test, test factory, test template, and lifecycle methods and test classes that are
 * annotated with it.
 *
 * Annotating a class is the same as annotating every test, test factory, and test template method (but not lifecycle
 * methods) of that class and its inner test classes, unless any of them is annotated with [CoroutinesTimeout], in which
 * case their annotation overrides the one on the containing class.
 *
 * Declaring [CoroutinesTimeout] on a test factory checks that it finishes in the specified time, but does not check
 * whether the methods that it produces obey the timeout as well.
 *
 * Example usage:
 * ```
 * @CoroutinesTimeout(100)
 * class CoroutinesTimeoutSimpleTest {
 *     // does not time out, as the annotation on the method overrides the class-level one
 *     @CoroutinesTimeout(1000)
 *     @Test
 *     fun classTimeoutIsOverridden() {
 *         runBlocking {
 *             delay(150)
 *         }
 *     }
 *
 *     // times out in 100 ms, timeout value is taken from the class-level annotation
 *     @Test
 *     fun classTimeoutIsUsed() {
 *         runBlocking {
 *             delay(150)
 *         }
 *     }
 * }
 * ```
 *
 * @see Timeout
 */
@ExtendWith(CoroutinesTimeoutExtension::class)
@Inherited
@MustBeDocumented
@ResourceLock("coroutines timeout", mode = ResourceAccessMode.READ)
@Retention(value = AnnotationRetention.RUNTIME)
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION)
public annotation class CoroutinesTimeout(
    val testTimeoutMs: Long,
    val cancelOnTimeout: Boolean = false
)
