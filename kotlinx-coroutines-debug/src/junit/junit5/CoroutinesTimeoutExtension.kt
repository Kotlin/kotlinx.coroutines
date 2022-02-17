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

internal class CoroutinesTimeoutException(val timeoutMs: Long): Exception("test timed out after $timeoutMs ms")

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
internal class CoroutinesTimeoutExtension internal constructor(
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
        /**
         * Creates the [CoroutinesTimeoutExtension] extension with the given timeout in seconds.
         */
        @JvmOverloads
        public fun seconds(timeout: Int, cancelOnTimeout: Boolean = false,
                           enableCoroutineCreationStackTraces: Boolean = true): CoroutinesTimeoutExtension =
            CoroutinesTimeoutExtension(enableCoroutineCreationStackTraces, timeout.toLong() * 1000, cancelOnTimeout)
    }

    /** @see [initialize] */
    private val debugProbesOwnershipPassed = AtomicBoolean(false)

    private fun tryPassDebugProbesOwnership() = debugProbesOwnershipPassed.compareAndSet(false, true)

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

    /**
     * Initialize this extension instance and/or the extension value store.
     *
     * It seems that the only way to reliably have JUnit5 clean up after its extensions is to put an instance of
     * [ExtensionContext.Store.CloseableResource] into the value store corresponding to the extension instance, which
     * means that [DebugProbes.uninstall] must be placed into the value store. [debugProbesOwnershipPassed] is `true`
     * if the call to [DebugProbes.install] performed in the constructor of the extension instance was matched with a
     * placing of [DebugProbes.uninstall] into the value store. We call the process of placing the cleanup procedure
     * "passing the ownership", as now JUnit5 (and not our code) has to worry about uninstalling the debug probes.
     *
     * However, extension instances can be reused with different value stores, and value stores can be reused across
     * extension instances. This leads to a tricky scheme of performing [DebugProbes.uninstall]:
     *
     * * If neither the ownership of this instance's [DebugProbes] was yet passed nor there is any cleanup procedure
     *   stored, it means that we can just store our cleanup procedure, passing the ownership.
     * * If the ownership was not yet passed, but a cleanup procedure is already stored, we can't just replace it with
     *   another one, as this would lead to imbalance between [DebugProbes.install] and [DebugProbes.uninstall].
     *   Instead, we know that this extension context will at least outlive this use of this instance, so some debug
     *   probes other than the ones from our constructor are already installed and won't be uninstalled during our
     *   operation. We simply uninstall the debug probes that were installed in our constructor.
     * * If the ownership was passed, but the store is empty, it means that this test instance is reused and, possibly,
     *   the debug probes installed in its constructor were already uninstalled. This means that we have to install them
     *   anew and store an uninstaller.
     */
    private fun initialize(extensionContext: ExtensionContext) {
        val store: ExtensionContext.Store = extensionContext.getStore(
            ExtensionContext.Namespace.create(CoroutinesTimeoutExtension::class, extensionContext.uniqueId))
        /** It seems that the JUnit5 documentation does not specify the relationship between the extension instances and
         * the corresponding [ExtensionContext] (in which the value stores are managed), so it is unclear whether it's
         * theoretically possible for two extension instances that run concurrently to share an extension context. So,
         * just in case this risk exists, we synchronize here. */
        synchronized(store) {
            if (store["debugProbes"] == null) {
                if (!tryPassDebugProbesOwnership()) {
                    /** This means that the [DebugProbes.install] call from the constructor of this extensions has
                     * already been matched with a corresponding cleanup procedure for JUnit5, but then JUnit5 cleaned
                     * everything up and later reused the same extension instance for other tests. Therefore, we need to
                     * install the [DebugProbes] anew. */
                    DebugProbes.enableCreationStackTraces = enableCoroutineCreationStackTraces
                    DebugProbes.install()
                }
                /** put a fake resource into this extensions's store so that JUnit cleans it up, uninstalling the
                 * [DebugProbes] after this extension instance is no longer needed. **/
                store.put("debugProbes", ExtensionContext.Store.CloseableResource { DebugProbes.uninstall() })
            } else if (!debugProbesOwnershipPassed.get()) {
                /** This instance shares its store with other ones. Because of this, there was no need to install
                 * [DebugProbes], they are already installed, and this fact will outlive this use of this instance of
                 * the extension. */
                if (tryPassDebugProbesOwnership()) {
                    // We successfully marked the ownership as passed and now may uninstall the extraneous debug probes.
                    DebugProbes.uninstall()
                }
            }
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