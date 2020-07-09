/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UNUSED", "INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import java.io.*
import java.lang.management.*
import kotlin.coroutines.*

/**
 * Debug probes support.
 *
 * Debug probes is a dynamic attach mechanism which installs multiple hooks into coroutines machinery.
 * It slows down all coroutine-related code, but in return provides a lot of diagnostic information, including
 * asynchronous stack-traces and coroutine dumps (similar to [ThreadMXBean.dumpAllThreads] and `jstack` via [DebugProbes.dumpCoroutines].
 * All introspecting methods throw [IllegalStateException] if debug probes were not installed.
 *
 * Installed hooks:
 *
 * * `probeCoroutineResumed` is invoked on every [Continuation.resume].
 * * `probeCoroutineSuspended` is invoked on every continuation suspension.
 * * `probeCoroutineCreated` is invoked on every coroutine creation using stdlib intrinsics.
 *
 * Overhead:
 *  * Every created coroutine is stored in a concurrent hash map and hash map is looked up and
 *    updated on each suspension and resumption.
 *  * If [DebugProbes.enableCreationStackTraces] is enabled, stack trace of the current thread is captured on
 *    each created coroutine that is a rough equivalent of throwing an exception per each created coroutine.
 */
@ExperimentalCoroutinesApi
public object DebugProbes {

    /**
     * Whether coroutine creation stack traces should be sanitized.
     * Sanitization removes all frames from `kotlinx.coroutines` package except
     * the first one and the last one to simplify diagnostic.
     */
    public var sanitizeStackTraces: Boolean
        get() = DebugProbesImpl.sanitizeStackTraces
        set(value) {
            DebugProbesImpl.sanitizeStackTraces = value
        }

    /**
     * Whether coroutine creation stack traces should be captured.
     * When enabled, for each created coroutine a stack trace of the current
     * thread is captured and attached to the coroutine.
     * This option can be useful during local debug sessions, but is recommended
     * to be disabled in production environments to avoid stack trace dumping overhead.
     */
    public var enableCreationStackTraces: Boolean
        get() = DebugProbesImpl.enableCreationStackTraces
        set(value) {
            DebugProbesImpl.enableCreationStackTraces = value
        }

    /**
     * Determines whether debug probes were [installed][DebugProbes.install].
     */
    public val isInstalled: Boolean get() = DebugProbesImpl.isInstalled

    /**
     * Installs a [DebugProbes] instead of no-op stdlib probes by redefining
     * debug probes class using the same class loader as one loaded [DebugProbes] class.
     */
    public fun install() {
        DebugProbesImpl.install()
    }

    /**
     * Uninstall debug probes.
     */
    public fun uninstall() {
        DebugProbesImpl.uninstall()
    }

    /**
     * Invokes given block of code with installed debug probes and uninstall probes in the end.
     */
    public inline fun withDebugProbes(block: () -> Unit) {
        install()
        try {
            block()
        } finally {
            uninstall()
        }
    }

    /**
     * Returns string representation of the coroutines [job] hierarchy with additional debug information.
     * Hierarchy is printed from the [job] as a root transitively to all children.
     */
    public fun jobToString(job: Job): String = DebugProbesImpl.hierarchyToString(job)

    /**
     * Returns string representation of all coroutines launched within the given [scope].
     * Throws [IllegalStateException] if the scope has no a job in it.
     */
    public fun scopeToString(scope: CoroutineScope): String =
        jobToString(scope.coroutineContext[Job] ?: error("Job is not present in the scope"))

    /**
     * Prints [job] hierarchy representation from [jobToString] to the given [out].
     */
    public fun printJob(job: Job, out: PrintStream = System.out): Unit =
        out.println(DebugProbesImpl.hierarchyToString(job))

    /**
     * Prints all coroutines launched within the given [scope].
     * Throws [IllegalStateException] if the scope has no a job in it.
     */
    public fun printScope(scope: CoroutineScope, out: PrintStream = System.out): Unit =
       printJob(scope.coroutineContext[Job] ?: error("Job is not present in the scope"), out)

    /**
     * Returns all existing coroutines info.
     * The resulting collection represents a consistent snapshot of all existing coroutines at the moment of invocation.
     */
    public fun dumpCoroutinesInfo(): List<CoroutineInfo> = DebugProbesImpl.dumpCoroutinesInfo().map { CoroutineInfo(it) }

    /**
     * Dumps all active coroutines into the given output stream, providing a consistent snapshot of all existing coroutines at the moment of invocation.
     * The output of this method is similar to `jstack` or a full thread dump. It can be used as the replacement to
     * "Dump threads" action.
     *
     * Example of the output:
     * ```
     * Coroutines dump 2018/11/12 19:45:14
     *
     * Coroutine "coroutine#42":StandaloneCoroutine{Active}@58fdd99, state: SUSPENDED
     *     at MyClass$awaitData.invokeSuspend(MyClass.kt:37)
     * (Coroutine creation stacktrace)
     *     at MyClass.createIoRequest(MyClass.kt:142)
     *     at MyClass.fetchData(MyClass.kt:154)
     *     at MyClass.showData(MyClass.kt:31)
     * ...
     * ```
     */
    public fun dumpCoroutines(out: PrintStream = System.out): Unit = DebugProbesImpl.dumpCoroutines(out)
}

// Stubs which are injected as coroutine probes. Require direct match of signatures
internal fun probeCoroutineResumed(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineResumed(frame)

internal fun probeCoroutineSuspended(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineSuspended(frame)
internal fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> =
    DebugProbesImpl.probeCoroutineCreated(completion)
