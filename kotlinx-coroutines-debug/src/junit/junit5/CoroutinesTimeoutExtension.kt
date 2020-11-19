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

public class CoroutinesTimeoutException(public val timeoutMs: Long): Exception("test timed out ofter $timeoutMs ms")

public class CoroutinesTimeoutExtension internal constructor(
    private val enableCoroutineCreationStackTraces: Boolean = true,
    private val timeoutMs: Long? = null,
    private val cancelOnTimeout: Boolean? = null): InvocationInterceptor
{
    public constructor(timeoutMs: Long, cancelOnTimeout: Boolean = false,
                       enableCoroutineCreationStackTraces: Boolean = true):
        this(enableCoroutineCreationStackTraces, timeoutMs, cancelOnTimeout)

    public companion object {
        private val NAMESPACE: ExtensionContext.Namespace =
            ExtensionContext.Namespace.create("kotlinx", "coroutines", "debug", "junit5", "CoroutinesTimeout")

        @JvmOverloads
        public fun seconds(timeout: Int, cancelOnTimeout: Boolean = false,
                           enableCoroutineCreationStackTraces: Boolean = true): CoroutinesTimeoutExtension =
            CoroutinesTimeoutExtension(enableCoroutineCreationStackTraces, timeout.toLong() * 1000, cancelOnTimeout)
    }

    override fun <T : Any?> interceptTestClassConstructor(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Constructor<T>>,
        extensionContext: ExtensionContext
    ): T {
        val store: ExtensionContext.Store = extensionContext.getStore(NAMESPACE)
        if (store["debugProbes"] == null) {
            /** no [DebugProbes] uninstaller is present, so this must be the first test that this instance of
             * [CoroutinesTimeoutExtension] runs. Install the [DebugProbes]. */
            DebugProbes.enableCreationStackTraces = enableCoroutineCreationStackTraces
            DebugProbes.install()
            /** put a fake resource into this extensions's store so that JUnit cleans it up, uninstalling the
             * [DebugProbes] after this extension instance is no longer needed. **/
            store.put("debugProbes", ExtensionContext.Store.CloseableResource { DebugProbes.uninstall() })
        }
        return invocation.proceed()
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
        interceptLifecycleMethod(invocation, invocationContext)
    }

    override fun interceptAfterEachMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptLifecycleMethod(invocation, invocationContext)
    }

    override fun interceptBeforeAllMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptLifecycleMethod(invocation, invocationContext)
    }

    override fun interceptBeforeEachMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        interceptLifecycleMethod(invocation, invocationContext)
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

    private fun <T: Any?> interceptNormalMethod(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ): T {
        val annotation =
            AnnotationSupport.findAnnotation(invocationContext.executable, CoroutinesTimeout::class.java).or {
                extensionContext.testClass.flatMap { it.coroutinesTimeoutAnnotation() }
            }.orElseGet {
                throw UnsupportedOperationException("CoroutinesTimeoutExtension should not be used directly; annotate the test class or method with CoroutinesTimeout instead.")
            }
        return interceptInvocation(invocation, invocationContext.executable.name, annotation)
    }

    private fun interceptLifecycleMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>
    ) {
        val annotation =
            AnnotationSupport.findAnnotation(invocationContext.executable, CoroutinesTimeout::class.java).orElseGet {
                throw UnsupportedOperationException("CoroutinesTimeoutExtension should not be used directly; annotate the test class or method with CoroutinesTimeout instead.")
            }
        interceptInvocation(invocation, invocationContext.executable.name, annotation)
    }

    private fun <T : Any?> interceptInvocation(
        invocation: InvocationInterceptor.Invocation<T>,
        methodName: String,
        annotation: CoroutinesTimeout
    ): T =
        runWithTimeoutDumpingCoroutines(methodName, annotation.testTimeoutMs, annotation.cancelOnTimeout,
            { CoroutinesTimeoutException(annotation.testTimeoutMs) }, { invocation.proceed()})
}