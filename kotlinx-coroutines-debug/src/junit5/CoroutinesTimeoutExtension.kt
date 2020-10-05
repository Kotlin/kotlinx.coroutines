/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.debug.DebugProbes
import org.junit.jupiter.api.extension.BeforeAllCallback
import org.junit.jupiter.api.extension.ExtensionConfigurationException
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.api.extension.InvocationInterceptor
import org.junit.jupiter.api.extension.ReflectiveInvocationContext
import org.junit.platform.commons.JUnitException
import org.junit.platform.commons.support.AnnotationSupport
import org.junit.runner.*
import org.junit.runners.model.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream
import java.lang.reflect.Method
import java.time.Duration
import java.time.format.DateTimeParseException
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
        val annotation =
            AnnotationSupport.findAnnotation(invocationContext.executable, CoroutinesTimeout::class.java).or {
                AnnotationSupport.findAnnotation(extensionContext.testClass, CoroutinesTimeout::class.java)
            }.orElseGet {
                throw UnsupportedOperationException("CoroutinesTimeoutExtension should not be used directly; annotate the test class or method with CoroutinesTimeout instead.")
            }
        invocation.proceed()
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

    private fun interceptLifecycleMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        invocation.proceed()
    }

    override fun <T : Any?> interceptTestFactoryMethod(
        invocation: InvocationInterceptor.Invocation<T>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ): T = invocation.proceed()

    override fun interceptTestTemplateMethod(
        invocation: InvocationInterceptor.Invocation<Void>,
        invocationContext: ReflectiveInvocationContext<Method>,
        extensionContext: ExtensionContext
    ) {
        invocation.proceed()
    }

    private fun <T : Any?> interceptInvocation(
        invocation: InvocationInterceptor.Invocation<T>,
        methodName: String,
        annotation: CoroutinesTimeout
    ): T {
        val testStartedLatch = CountDownLatch(1)
        val testResult = FutureTask<T> {
            testStartedLatch.countDown()
            invocation.proceed()
        }
        val testThread = Thread(testResult, "Timeout test thread").apply { isDaemon = true }
        try {
            testThread.start()
            // Await until test is started to take only test execution time into account
            testStartedLatch.await()
            return testResult.get(annotation.testTimeoutMs, TimeUnit.MILLISECONDS)
        } catch (e: TimeoutException) {
            handleTimeout(methodName, testThread, annotation)
        } catch (e: ExecutionException) {
            throw e.cause ?: e
        } finally {
            DebugProbes.uninstall()
        }
    }

    private fun handleTimeout(methodName: String, testThread: Thread, annotation: CoroutinesTimeout): Nothing {
        val units =
            if (annotation.testTimeoutMs % 1000 == 0L)
                "${annotation.testTimeoutMs / 1000} seconds"
            else "$annotation.testTimeoutMs milliseconds"

        System.err.println("\nTest $methodName timed out after $units\n")
        System.err.flush()

        DebugProbes.dumpCoroutines()
        System.out.flush() // Synchronize serr/sout

        /*
         * Order is important:
         * 1) Create exception with a stacktrace of hang test
         * 2) Cancel all coroutines via debug agent API (changing system state!)
         * 3) Throw created exception
         */
        val exception = createTimeoutException(testThread, annotation.testTimeoutMs)
        cancelIfNecessary(annotation.cancelOnTimeout)
        // If timed out test throws an exception, we can't do much except ignoring it
        throw exception
    }

    private fun cancelIfNecessary(cancelOnTimeout: Boolean) {
        if (cancelOnTimeout) {
            DebugProbes.dumpCoroutinesInfo().forEach {
                it.job?.cancel()
            }
        }
    }

    private fun createTimeoutException(thread: Thread, testTimeoutMs: Long): Exception {
        val stackTrace = thread.stackTrace
        val exception = TestTimedOutException(testTimeoutMs, TimeUnit.MILLISECONDS)
        exception.stackTrace = stackTrace
        thread.interrupt()
        return exception
    }
}