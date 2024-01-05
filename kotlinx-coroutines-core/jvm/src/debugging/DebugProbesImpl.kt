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
     * TODO: maybe should be renamed
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

    @Suppress("UNCHECKED_CAST")
    public fun getContinuationStackWithSpilledVariables(coroutineStackFrame: CoroutineStackFrame): List<StackTraceFrame> {
        // go up the stack, collect spilled variables via DebugMetadata
        val debugMetadataClass = Class.forName("kotlin.coroutines.jvm.internal.DebugMetadataKt")
        val baseContinuationImplClass = Class.forName("kotlin.coroutines.jvm.internal.BaseContinuationImpl")
        val getSpilledVariables = debugMetadataClass.getDeclaredMethod("getSpilledVariableFieldMapping", baseContinuationImplClass)
        val getStackTraceElement = debugMetadataClass.getDeclaredMethod("getStackTraceElement", baseContinuationImplClass)
        
        val continuationStack = mutableListOf<StackTraceFrame>()
        var completion: CoroutineStackFrame? = coroutineStackFrame
        while (completion != null) {
            val spilledVariables: Array<String> = getSpilledVariables.invoke(null, coroutineStackFrame) as Array<String>
            val stackTraceElement = getStackTraceElement.invoke(null, coroutineStackFrame) as StackTraceElement
            continuationStack.add(StackTraceFrame(completion.callerFrame, stackTraceElement, spilledVariables))
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
