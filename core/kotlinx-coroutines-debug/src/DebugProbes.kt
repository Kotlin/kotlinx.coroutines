/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import net.bytebuddy.*
import net.bytebuddy.agent.*
import net.bytebuddy.dynamic.loading.*
import java.io.*
import java.lang.management.*
import java.text.*
import java.util.*
import kotlin.collections.ArrayList
import kotlin.coroutines.*

/**
 * Debug probes support.
 *
 * Debug probes is a dynamic attach mechanism, which installs multiple hooks into [Continuation] machinery.
 * It significantly slows down all coroutine-related code, but in return provides a lot of debug information, including
 * asynchronous stack-traces and coroutine dumps (similar to [ThreadMXBean.dumpAllThreads] and `jstack` via [DebugProbes.dumpCoroutines].
 *
 * Installed hooks:
 *
 * * `probeCoroutineResumed` is invoked on every [Continuation.resume].
 * * `probeCoroutineSuspended` is invoked on every continuation suspension.
 * * `probeCoroutineCreated` is invoked on every coroutine creation using stdlib intrinsics.
 *
 * Overhead:
 *  * Every created continuation is stored in a weak hash map, thus adding additional GC pressure.
 *  * On every created continuation, stacktrace of the current thread is dumped.
 *  * On every `resume` and `suspend`, [WeakHashMap] is updated under a global lock.
 *
 * **WARNING: DO NOT USE DEBUG PROBES IN PRODUCTION ENVIRONMENT.**
 */
public object DebugProbes {

    private val dateFormat = SimpleDateFormat("yyyy/MM/dd HH:mm:ss")
    private val capturedCoroutines = WeakHashMap<ArtificialStackFrame<*>, CoroutineState>()
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

        installed = false
        capturedCoroutines.clear()
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

    /**
     * Returns all alive coroutine states.
     * Resulting collection represents consistent snapshot of all alive coroutines at the moment of invocation.
     */
    @Synchronized
    public fun dumpCoroutinesState(): List<CoroutineState> = capturedCoroutines.entries.map {
        CoroutineState(it.key, it.value.creationStackTrace,  it.value._state, it.value.lastObservedFrame)
    }

    @Synchronized
    public fun dumpCoroutines(out: PrintStream = System.out): Unit {
        // Avoid inference with other out/err invocations
        val resultingString = buildString {
            append("Coroutines dump ${dateFormat.format(System.currentTimeMillis())}:\n")

            capturedCoroutines.forEach { key, value ->
                val state = if (value.state == State.RUNNING)
                    "${value.state} (Last suspension stacktrace, not an actual stacktrace)"
                else value.state.toString()

                append("\nCoroutine $key, state: $state")
                if (value.lastObservedFrame == null) {
                    append("\n\tat ${artificialFrame("Coroutine creation callsite")}")
                    printStackTrace(value.creationStackTrace)

                } else {
                    printStackTrace(value.suspensionStackTrace())
                }
            }
        }

        out.println(resultingString)
    }

    private fun StringBuilder.printStackTrace(frames: List<StackTraceElement>) {
        frames.forEach { frame ->
            append("\n\tat $frame")
        }
    }

    @Synchronized
    internal fun probeCoroutineResumed(frame: Continuation<*>) = updateState(frame, State.RUNNING)

    @Synchronized
    internal fun probeCoroutineSuspended(frame: Continuation<*>) = updateState(frame, State.SUSPENDED)

    /*
     * Updates coroutine state.
     * TODO this method is currently racy:
     *
     * ```
     * suspendCoroutineUninterceptedOrReturn<Int> {
     *   publish(it)
     *   ready.compareAndSet(false, true)
     *   COROUTINE_SUSPENDED
     * }
     *
     * fun onPublishInAnotherThread(continuation: Continuation<*>) {
     *   continuation.resume(Result.success(...))
     * }
     * ```
     */
    private fun updateState(frame: Continuation<*>, state: State) {
        val owner = frame.owner() ?: return
        val coroutineState = capturedCoroutines[owner] ?: return
        coroutineState._state = state
        coroutineState.lastObservedFrame = frame
    }

    private fun Continuation<*>.owner(): ArtificialStackFrame<*>? {
        var frame = this as? CoroutineStackFrame ?: return null
        while (true) {
            if (frame is ArtificialStackFrame<*>) return frame
            val completion = frame.callerFrame ?: return null
            frame = completion
        }
    }

    @Synchronized
    internal fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> {
        val stacktrace = sanitizedStackTrace(Exception())

        // TODO create lazy proxy and reverse stacktrace on demand
        val frames = ArrayList<CoroutineStackFrame?>(stacktrace.size)
        for ((index, frame) in stacktrace.reversed().withIndex()) {
            frames += object : CoroutineStackFrame {
                override val callerFrame: CoroutineStackFrame?
                    get() = if (index == 0) null else frames[index - 1]

                override fun getStackTraceElement(): StackTraceElement = frame
            }
        }

        val result = ArtificialStackFrame(completion, frames.last()!!)
        capturedCoroutines[result] = CoroutineState(completion, stacktrace.slice(1 until stacktrace.size))
        return result
    }

    @Synchronized
    private fun probeCoroutineCompleted(coroutine: ArtificialStackFrame<*>) {
        capturedCoroutines.remove(coroutine)
    }

    private class ArtificialStackFrame<T>(val delegate: Continuation<T>, frame: CoroutineStackFrame) :
        Continuation<T> by delegate, CoroutineStackFrame by frame {

        override fun resumeWith(result: Result<T>) {
            probeCoroutineCompleted(this)
            delegate.resumeWith(result)
        }

        override fun toString(): String = delegate.toString()
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
