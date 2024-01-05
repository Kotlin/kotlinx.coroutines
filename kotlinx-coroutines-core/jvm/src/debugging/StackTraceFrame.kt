/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debugging

import kotlin.coroutines.jvm.internal.CoroutineStackFrame

public class StackTraceFrame internal constructor(
    override val callerFrame: CoroutineStackFrame?,
    // Used by the IDEA debugger via reflection and must be kept binary-compatible, see KTIJ-24102
    @JvmField public val stackTraceElement: StackTraceElement,
    public val spilledVariables: Array<String>
) : CoroutineStackFrame {
    override fun getStackTraceElement(): StackTraceElement = stackTraceElement
}
