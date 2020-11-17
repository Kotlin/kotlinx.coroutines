/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.debug.*
import kotlinx.coroutines.debug.runWithTimeoutDumpingCoroutines
import org.junit.jupiter.api.extension.*
import org.junit.platform.commons.support.AnnotationSupport
import java.lang.reflect.*

public class CoroutinesTimeoutException(public val timeoutMs: Long): Exception("test timed out ofter $timeoutMs ms")

public class CoroutinesTimeoutExtension internal constructor(): InvocationInterceptor {

    private companion object {
        val NAMESPACE = ExtensionContext.Namespace.create("kotlinx", "coroutines", "debug", "junit5",
            "CoroutinesTimeout")
    }

    override fun <T : Any?> interceptTestClassConstructor(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Constructor<T>>,
        extensionContext: ExtensionContext
    ): T {
        if (extensionContext.getStore(NAMESPACE)["debugProbes"] == null) {
            DebugProbes.install()
            val uninstall: ExtensionContext.Store.CloseableResource = ExtensionContext.Store.CloseableResource {
                DebugProbes.uninstall()
            }
            extensionContext.getStore(NAMESPACE).put("debugProbes", uninstall)
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

    private fun <T: Any?> interceptNormalMethod(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ): T {
        val annotation =
            AnnotationSupport.findAnnotation(invocationContext.executable, CoroutinesTimeout::class.java).or {
                AnnotationSupport.findAnnotation(extensionContext.testClass, CoroutinesTimeout::class.java)
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
    ): T {
        DebugProbes.enableCreationStackTraces = annotation.enableCoroutineCreationStackTraces
        return try {
            runWithTimeoutDumpingCoroutines(methodName, annotation.testTimeoutMs, annotation.cancelOnTimeout,
                { CoroutinesTimeoutException(annotation.testTimeoutMs) }
            ) {
                invocation.proceed()
            }
        }
    }
}