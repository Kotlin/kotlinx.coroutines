/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import java.io.*
import java.lang.management.*
import java.util.*
import kotlin.coroutines.*

/**
 * Debug probes support.
 *
 * Debug probes is a dynamic attach mechanism, which installs multiple hooks into [Continuation] machinery.
 * It slows down all coroutine-related code, but in return provides a lot of debug information, including
 * asynchronous stack-traces and coroutine dumps (similar to [ThreadMXBean.dumpAllThreads] and `jstack` via [DebugProbes.dumpCoroutines].
 *
 * Installed hooks:
 *
 * * `probeCoroutineResumed` is invoked on every [Continuation.resume].
 * * `probeCoroutineSuspended` is invoked on every continuation suspension.
 * * `probeCoroutineCreated` is invoked on every coroutine creation using stdlib intrinsics.
 *
 * Overhead:
 *  * Every created coroutine is stored in a weak hash map, thus adding additional GC pressure.
 *  * On every created coroutine, stacktrace of the current thread is dumped.
 *  * On every `resume` and `suspend`, [WeakHashMap] is updated under a global lock.
 *
 * **WARNING: DO NOT USE DEBUG PROBES IN PRODUCTION ENVIRONMENT.**
 */
@ExperimentalCoroutinesApi
public object DebugProbes {

    /**
     * Whether coroutine creation stacktraces should be sanitized.
     * Sanitization removes all frames from `kotlinx.coroutines` package except
     * the first one and the last one to simplify user's diagnostic.
     */
    public var sanitizeStackTraces: Boolean = true

    /**
     * Installs a [DebugProbes] instead of no-op stdlib probes by redefining
     * debug probes class using the same class loader as one loaded [DebugProbes] class.
     *
     * **WARNING: DO NOT USE DEBUG PROBES IN PRODUCTION ENVIRONMENT**
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
     *
     * **WARNING: DO NOT USE DEBUG PROBES IN PRODUCTION ENVIRONMENT**
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
    public fun hierarchyToString(job: Job): String = DebugProbesImpl.hierarchyToString(job)

    /**
     * Prints [job] hierarchy representation from [hierarchyToString] to given [out].
     */
    public fun printHierarchy(job: Job, out: PrintStream = System.out) =
        out.println(DebugProbesImpl.hierarchyToString(job))

    /**
     * Returns all alive coroutine states.
     * Resulting collection represents a consistent snapshot of all alive coroutines at the moment of invocation.
     */
    public fun dumpCoroutinesState(): List<CoroutineState> = DebugProbesImpl.dumpCoroutinesState()

    /**
     * Dumps all active coroutines into given output stream.
     * Resulting collection represents a consistent snapshot of all alive coroutines at the moment of invocation.
     * Output of this method is similar to `jstack` or full thread dump, so this method can and should be used as replacement to
     * "Dump threads" action
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
     *
     * ...
     * ```
     */
    public fun dumpCoroutines(out: PrintStream = System.out) = DebugProbesImpl.dumpCoroutines(out)
}

// Stubs which are injected as coroutine probes. Require direct match of signatures
internal fun probeCoroutineResumed(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineResumed(frame)

internal fun probeCoroutineSuspended(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineSuspended(frame)
internal fun <T> probeCoroutineCreated(completion: kotlin.coroutines.Continuation<T>): kotlin.coroutines.Continuation<T> =
    DebugProbesImpl.probeCoroutineCreated(completion)
