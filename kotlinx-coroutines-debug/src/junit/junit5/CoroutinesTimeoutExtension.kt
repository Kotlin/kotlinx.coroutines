/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.debug.*
import kotlinx.coroutines.debug.runWithTimeoutDumpingCoroutines
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.api.extension.InvocationInterceptor
import org.junit.jupiter.api.extension.ReflectiveInvocationContext
import org.junit.platform.commons.support.AnnotationSupport
import org.junit.runners.model.*
import java.lang.reflect.Method
import java.util.concurrent.CountDownLatch
import java.util.concurrent.ExecutionException
import java.util.concurrent.FutureTask
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

public class CoroutinesTimeoutExtension: InvocationInterceptor {

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
        DebugProbes.install()
        return try {
            runWithTimeoutDumpingCoroutines(methodName, annotation.testTimeoutMs, annotation.cancelOnTimeout) {
                invocation.proceed()
            }
        } finally {
            DebugProbes.uninstall()
        }
    }
}