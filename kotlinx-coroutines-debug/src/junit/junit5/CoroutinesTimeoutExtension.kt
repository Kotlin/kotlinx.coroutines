/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.debug.*
import kotlinx.coroutines.debug.runWithTimeoutDumpingCoroutines
import org.junit.jupiter.api.extension.*
import org.junit.platform.commons.support.AnnotationSupport
import java.lang.reflect.*
import java.util.*
import java.util.concurrent.atomic.*

public class CoroutinesTimeoutException(public val timeoutMs: Long): Exception("test timed out ofter $timeoutMs ms")

/**
 * This JUnit5 extension allows running test, test factory, test template, and lifecycle methods in a separate thread,
 * failing them after the provided time limit and interrupting the thread.
 *
 * Additionally, it installs [DebugProbes] and dumps all coroutines at the moment of the timeout. It also cancels
 * coroutines on timeout if [cancelOnTimeout] set to `true`.
 * [enableCoroutineCreationStackTraces] controls the corresponding [DebugProbes.enableCreationStackTraces] property
 * and can be optionally disabled to speed-up tests if creation stack traces are not needed.
 *
 * Beware that if several tests that use this extension set [enableCoroutineCreationStackTraces] to different values and
 * execute in parallel, the behavior is ill-defined. In order to avoid conflicts between different instances of this
 * extension when using JUnit5 in parallel, use [ResourceLock] with resource name `coroutines timeout` on tests that use
 * it. Note that the tests annotated with [CoroutinesTimeout] already use this [ResourceLock], so there is no need to
 * annotate them additionally.
 *
 * Note that while calls to test factories are verified to finish in the specified time, but the methods that they
 * produce are not affected by this extension.
 *
 * Beware that registering the extension via [CoroutinesTimeout] annotation conflicts with manually registering it on
 * the same tests via other methods (most notably, [RegisterExtension]) and is prohibited.
 *
 * Example of usage:
 * ```
 * class HangingTest {
 *     @JvmField
 *     @RegisterExtension
 *     val timeout = CoroutinesTimeoutExtension.seconds(5)
 *
 *     @Test
 *     fun testThatHangs() = runBlocking {
 *          ...
 *          delay(Long.MAX_VALUE) // somewhere deep in the stack
 *          ...
 *     }
 * }
 * ```
 *
 * @see [CoroutinesTimeout]
 * */
// NB: the constructor is not private so that JUnit is able to call it via reflection.
public class CoroutinesTimeoutExtension internal constructor(
    private val enableCoroutineCreationStackTraces: Boolean = true,
    private val timeoutMs: Long? = null,
    private val cancelOnTimeout: Boolean? = null): InvocationInterceptor
{
    /**
     * Creates the [CoroutinesTimeoutExtension] extension with the given timeout in milliseconds.
     */
    public constructor(timeoutMs: Long, cancelOnTimeout: Boolean = false,
                       enableCoroutineCreationStackTraces: Boolean = true):
        this(enableCoroutineCreationStackTraces, timeoutMs, cancelOnTimeout)

    public companion object {
        private val NAMESPACE: ExtensionContext.Namespace =
            ExtensionContext.Namespace.create("kotlinx", "coroutines", "debug", "junit5", "CoroutinesTimeout")

        /**
         * Creates the [CoroutinesTimeoutExtension] extension with the given timeout in seconds.
         */
        @JvmOverloads
        public fun seconds(timeout: Int, cancelOnTimeout: Boolean = false,
                           enableCoroutineCreationStackTraces: Boolean = true): CoroutinesTimeoutExtension =
            CoroutinesTimeoutExtension(enableCoroutineCreationStackTraces, timeout.toLong() * 1000, cancelOnTimeout)
    }

    private val debugProbesOwnershipPassed = AtomicBoolean(false)

    /* We install the debug probes early so that the coroutines launched from the test constructor are captured as well.
    However, this is not enough as the same extension instance may be reused several times, even cleaning up its
    resources from the store. */
    init {
        DebugProbes.enableCreationStackTraces = enableCoroutineCreationStackTraces
        DebugProbes.install()
    }

    // This is needed so that a class with no tests still successfully passes the ownership of DebugProbes to JUnit5.
    override fun <T : Any?> interceptTestClassConstructor(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Constructor<T>>,
        extensionContext: ExtensionContext
    ): T {
        initialize(extensionContext)
        return invocation.proceed()
    }

    private fun initialize(extensionContext: ExtensionContext) {
        val store: ExtensionContext.Store = extensionContext.getStore(NAMESPACE)
        if (store["debugProbes"] == null) {
            if (!debugProbesOwnershipPassed.compareAndSet(false, true)) {
                /** This means that the [DebugProbes.install] call from the constructor of this extensions has already
                 * been matched with a corresponding cleanup procedure for JUnit5, but then JUnit5 cleaned everything up
                 * and later reused the same extension instance for other tests. Therefore, we need to install the
                 * [DebugProbes] anew. */
                DebugProbes.enableCreationStackTraces = enableCoroutineCreationStackTraces
                DebugProbes.install()
            }
            /** put a fake resource into this extensions's store so that JUnit cleans it up, uninstalling the
             * [DebugProbes] after this extension instance is no longer needed. **/
            store.put("debugProbes", ExtensionContext.Store.CloseableResource { DebugProbes.uninstall() })
        }
    }

    override fun interceptTestMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptNormalMethod(invocation, invocationContext, extensionContext)
    }

    override fun interceptAfterAllMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptLifecycleMethod(invocation, invocationContext, extensionContext)
    }

    override fun interceptAfterEachMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptLifecycleMethod(invocation, invocationContext, extensionContext)
    }

    override fun interceptBeforeAllMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptLifecycleMethod(invocation, invocationContext, extensionContext)
    }

    override fun interceptBeforeEachMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptLifecycleMethod(invocation, invocationContext, extensionContext)
    }

    override fun <T : Any?> interceptTestFactoryMethod(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ): T = interceptNormalMethod(invocation, invocationContext, extensionContext)

    override fun interceptTestTemplateMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptNormalMethod(invocation, invocationContext, extensionContext)
    }

    private fun<T> Class<T>.coroutinesTimeoutAnnotation(): Optional<CoroutinesTimeout> =
        AnnotationSupport.findAnnotation(this, CoroutinesTimeout::class.java).or {
            enclosingClass?.coroutinesTimeoutAnnotation() ?: Optional.empty()
        }

    private fun <T: Any?> interceptMethod(
        useClassAnnotation: Boolean,
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ): T {
        initialize(extensionContext)
        val testAnnotationOptional =
            AnnotationSupport.findAnnotation(invocationContext.executable, CoroutinesTimeout::class.java)
        val classAnnotationOptional = extensionContext.testClass.flatMap { it.coroutinesTimeoutAnnotation() }
        if (timeoutMs != null && cancelOnTimeout != null) {
            // this means we @RegisterExtension was used in order to register this extension.
            if (testAnnotationOptional.isPresent || classAnnotationOptional.isPresent) {
                /* Using annotations creates a separate instance of the extension, which composes in a strange way: both
                timeouts are applied. This is at odds with the concept that method-level annotations override the outer
                rules and may lead to unexpected outcomes, so we prohibit this. */
                throw UnsupportedOperationException("Using CoroutinesTimeout along with instance field-registered CoroutinesTimeout is prohibited; please use either @RegisterExtension or @CoroutinesTimeout, but not both")
            }
            return interceptInvocation(invocation, invocationContext.executable.name, timeoutMs, cancelOnTimeout)
        }
        /* The extension was registered via an annotation; check that we succeeded in finding the annotation that led to
        the extension being registered and taking its parameters. */
        if (testAnnotationOptional.isEmpty && classAnnotationOptional.isEmpty) {
            throw UnsupportedOperationException("Timeout was registered with a CoroutinesTimeout annotation, but we were unable to find it. Please report this.")
        }
        return when {
            testAnnotationOptional.isPresent -> {
                val annotation = testAnnotationOptional.get()
                interceptInvocation(invocation, invocationContext.executable.name, annotation.testTimeoutMs,
                    annotation.cancelOnTimeout)
            }
            useClassAnnotation && classAnnotationOptional.isPresent -> {
                val annotation = classAnnotationOptional.get()
                interceptInvocation(invocation, invocationContext.executable.name, annotation.testTimeoutMs,
                    annotation.cancelOnTimeout)
            }
            else -> {
                invocation.proceed()
            }
        }
    }

    private fun<T> interceptNormalMethod(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ): T = interceptMethod(true, invocation, invocationContext, extensionContext)

    private fun interceptLifecycleMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) = interceptMethod(false, invocation, invocationContext, extensionContext)

    private fun <T : Any?> interceptInvocation(
        invocation: InvocationInterceptor.Invocation<T>,
        methodName: String,
        testTimeoutMs: Long,
        cancelOnTimeout: Boolean
    ): T =
        runWithTimeoutDumpingCoroutines(methodName, testTimeoutMs, cancelOnTimeout,
            { CoroutinesTimeoutException(testTimeoutMs) }, { invocation.proceed() })
}