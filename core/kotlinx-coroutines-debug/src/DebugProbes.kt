/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.CoroutineStackFrame
import net.bytebuddy.*
import net.bytebuddy.agent.*
import net.bytebuddy.dynamic.loading.*
import java.lang.management.*
import java.util.*
import kotlin.collections.ArrayList
import kotlin.coroutines.*

/**
 * Debug probes support.
 *
 * Debug probes is a dynamic attach mechanism, which installs multiple hooks into [Continuation] machinery.
 * It significantly slows down all coroutine-related code, but in return provides a lot of debug information, including
 * asynchronous stack-traces and coroutine dumps (similar to [ThreadMXBean.dumpAllThreads] and `jstack`.
 *
 * Installed hooks:
 *
 * * `probeCoroutineResumed` is invoked on every [Continuation.resume].
 * * `probeCoroutineSuspended` is invoked on every continuation suspension.
 * * `probeCoroutineCreated` is invoked on every coroutine creation using stdlib intrinsics.
 *
 * Overhead:
 *  * Every created continuation is stored in a weak hash map, thus adding additional GC pressure
 *  * On every created continuation, stacktrace of the current thread is dumped
 *  * On every `resume` and `suspend`, [WeakHashMap] is updated under a global lock
 *
 * **WARNING: DO NOT USE DEBUG PROBES IN PRODUCTION ENVIRONMENT**
 */
public object DebugProbes {
    private val traces = WeakHashMap<Continuation<*>, Array<StackTraceElement>>()
    private var installed: Boolean = false

    /**
     * Installs a [DebugProbes] instead of no-op stdlib probes by redefining
     * debug probes class using the same class loader.
     *
     * **WARNING: DO NOT USE DEBUG PROBES IN PRODUCTION ENVIRONMENT**
     * Subsequent invocations of this method have no effect.
     */
    @Synchronized
    public fun install() {
        if (installed) {
            return
        }

        installed = true
        ByteBuddyAgent.install()
        val cl = Class.forName("kotlin.coroutines.jvm.internal.DebugProbesKt")
        val cl2 = Class.forName("kotlinx.coroutines.DebugProbesKt")

        ByteBuddy()
            .redefine(cl2)
            .name(cl.name)
            .make()
            .load(cl.classLoader, ClassReloadingStrategy.fromInstalledAgent())
    }

    /**
     * Uninstall debug probes
     */
    @Synchronized
    public fun uninstall() {
        if (!installed) {
            return
        }

        traces.clear()
        ByteBuddyAgent.install()
        val cl = Class.forName("kotlin.coroutines.jvm.internal.DebugProbesKt")
        val cl2 = Class.forName("kotlinx.coroutines.NoOpProbesKt")

        ByteBuddy()
            .redefine(cl2)
            .name(cl.name)
            .make()
            .load(cl.classLoader, ClassReloadingStrategy.fromInstalledAgent())
    }

    /**
     * Invokes given block of code with installed debug probes and unistall probes in the end.
     * **NOTE:** this method is not composable, it will uninstall debug probes even if they were installed
     * prior to method invocation
     */
    public inline fun withDebugProbes(block: () -> Unit) {
        install()
        try {
            block()
        } finally {
            uninstall()
        }
    }


    public fun dumpCoroutines(): String = TODO("Not implemented")

    @Synchronized
    internal fun probeCoroutineResumed(frame: Continuation<*>) {
    }

    @Synchronized
    internal fun probeCoroutineSuspended(frame: Continuation<*>) {
    }

    @Synchronized
    internal fun <T> probeCoroutineCreated(completion: kotlin.coroutines.Continuation<T>): kotlin.coroutines.Continuation<T> {
        val stacktrace = sanitizedStackTrace(Exception())
        traces[completion] = stacktrace

        // TODO create lazy proxy and reverse stacktrace on demand
        val frames = ArrayList<CoroutineStackFrame?>(stacktrace.size)
        for ((index, frame) in stacktrace.reversed().withIndex()) {
            frames += object : CoroutineStackFrame {
                override val callerFrame: CoroutineStackFrame?
                    get() = if (index == 0) null else frames[index - 1]

                override fun getStackTraceElement(): StackTraceElement = frame
            }
        }

        return object : Continuation<T> by completion, CoroutineStackFrame by frames.last()!! {}
    }

    private fun <T : Throwable> sanitizedStackTrace(throwable: T): Array<StackTraceElement> {
        val stackTrace = throwable.stackTrace
        val size = stackTrace.size

        var lastIntrinsic = -1
        for (i in 0 until size) {
            val name = stackTrace[i].className
            if ("kotlin.coroutines.jvm.internal.DebugProbesKt" == name) {
                lastIntrinsic = i
            }
        }

        val startIndex = lastIntrinsic + 1
        return Array(size - lastIntrinsic) {
            if (it == 0) {
                artificialFrame("Coroutine creation callsite")
            } else {
                stackTrace[startIndex + it - 1]
            }
        }
    }
}

// Stubs which are injected as coroutine probes. Require direct match of signatures
internal fun probeCoroutineResumed(frame: Continuation<*>) = DebugProbes.probeCoroutineResumed(frame)
internal fun probeCoroutineSuspended(frame: Continuation<*>) = DebugProbes.probeCoroutineSuspended(frame)
internal fun <T> probeCoroutineCreated(completion: kotlin.coroutines.Continuation<T>): kotlin.coroutines.Continuation<T> =
    DebugProbes.probeCoroutineCreated(completion)
