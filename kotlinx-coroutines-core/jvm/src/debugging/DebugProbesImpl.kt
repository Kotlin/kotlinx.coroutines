/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debugging


import kotlinx.coroutines.debug.internal.DebugProbesImpl
import kotlin.coroutines.jvm.internal.CoroutineStackFrame
import kotlinx.coroutines.internal.StackTraceElement
import kotlin.coroutines.*

public object DebugProbesImpl {
    private val delegate = DebugProbesImpl
    private val debugMetadataClass = Class.forName("kotlin.coroutines.jvm.internal.DebugMetadataKt")
    private val baseContinuationImplClass = Class.forName("kotlin.coroutines.jvm.internal.BaseContinuationImpl")
    private val getSpilledVariables = debugMetadataClass.getDeclaredMethod("getSpilledVariableFieldMapping", baseContinuationImplClass)
    private val getStackTraceElement = debugMetadataClass.getDeclaredMethod("getStackTraceElement", baseContinuationImplClass)

    /**
     * Whether DebugProbes are installed.
     */
    public val isInstalled: Boolean = delegate.isInstalled
    
    /*
     * This method optimises the number of packages sent by the IDEA debugger
     * to a client VM to speed up fetching of coroutine information.
     *
     * The return value is an array of objects, which consists of four elements:
     * 1) A string in a JSON format that stores information that is needed to display
     *    every coroutine in the coroutine panel in the IDEA debugger.
     * 2) An array of last observed threads.
     * 3) An array of last observed frames.
     * 4) An array of DebugCoroutineInfo.
     *
     * ### Implementation note
     * For methods like `dumpCoroutinesInfo` JDWP provides `com.sun.jdi.ObjectReference`
     * that does a roundtrip to client VM for *each* field or property read.
     * To avoid that, we serialize most of the critical for UI data into a primitives
     * to save an exponential number of roundtrips.
     * 
     * NOTE: Used in IDEA in CoroutinesInfoFromJsonAndReferencesProvider in priority to dumpCoroutinesInfo
     * TODO: should be renamed
     */
    public fun dumpCoroutinesInfoAsJsonAndReferences(): Array<Any> = delegate.dumpCoroutinesInfoAsJsonAndReferences()

    /**
     * Get DebugCoroutineInfo for the given continuation.
     * Goes up the continuation stack, till it reaches the completion of top level continuation which is an instance of CoroutineOwner.
     * CoroutineOwner contains the coroutine information.
     */
    public fun getDebugCoroutineInfo(coroutineStackFrame: CoroutineStackFrame): DebugCoroutineInfo? {
        var completion: CoroutineStackFrame? = coroutineStackFrame
        while (completion != null) {
            if (completion is DebugProbesImpl.CoroutineOwner<*>) {
                completion.info.context?.let { context -> 
                    return DebugCoroutineInfo((completion as DebugProbesImpl.CoroutineOwner<*>).info, context)
                }
            }
            completion = completion.callerFrame
        }
        return null
    }
    
    /**
     * Gets the continuation stack of BaseContinuationImpl instances starting from the given [coroutineStackFrame] up to the parent continuation.
     * Adds spilled variables for every frame that is an instance of BaseContinuationImpl.
     */
    @Suppress("UNCHECKED_CAST")
    public fun getContinuationStackWithSpilledVariables(coroutineStackFrame: CoroutineStackFrame): List<StackTraceFrame> {
        val continuationStack = mutableListOf<StackTraceFrame>()
        var completion: CoroutineStackFrame? = coroutineStackFrame
        while (completion != null) {
            // top-level completion reached, return the continuation stack
            // Note: https://github.com/JetBrains/kotlin/blob/65244b4bea81f737466618927d4f3afe339cad0d/libraries/stdlib/jvm/src/kotlin/coroutines/jvm/internal/ContinuationImpl.kt#L45
            if (!baseContinuationImplClass.isInstance(completion)) break
            val spilledVariables: Array<String> = getSpilledVariables.invoke(null, completion) as Array<String>
            val stackTraceElement = getStackTraceElement.invoke(null, completion) as StackTraceElement
            continuationStack.add(StackTraceFrame(completion, stackTraceElement, spilledVariables))
            completion = completion.callerFrame
        }
        return continuationStack
    }

    /**
     * Whether to ignore coroutines whose context is [EmptyCoroutineContext].
     *
     * Coroutines with empty context are considered to be irrelevant for the concurrent coroutines' observability:
     * - They do not contribute to any concurrent executions
     * - They do not contribute to the (concurrent) system's liveness and/or deadlocks, as no other coroutines might wait for them
     * - The typical usage of such coroutines is a combinator/builder/lookahead parser that can be debugged using more convenient tools.
     *
     * `true` by default.
     */
    public var ignoreCoroutinesWithEmptyContext: Boolean = delegate.ignoreCoroutinesWithEmptyContext

    /**
     * Whether coroutine creation stack traces should be captured.
     * When enabled, for each created coroutine a stack trace of the current
     * thread is captured and attached to the coroutine.
     * This option can be useful during local debug sessions, but is recommended
     * to be disabled in production environments to avoid stack trace dumping overhead.
     *
     * `true` by default.
     */
    public var enableCreationStackTraces: Boolean = delegate.enableCreationStackTraces

    /**
     * Whether coroutine creation stack traces should be sanitized.
     * Sanitization removes all frames from `kotlinx.coroutines` package except
     * the first one and the last one to simplify diagnostic.
     *
     * `true` by default.
     */
    public var sanitizeStackTraces: Boolean = delegate.sanitizeStackTraces
}
