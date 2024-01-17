/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debugging

import kotlin.coroutines.jvm.internal.CoroutineStackFrame

// TODO: rename to DebuggingCoroutineTraceFrame
public class StackTraceFrame internal constructor(
    override val callerFrame: CoroutineStackFrame?,
    @JvmField
    public val stackTraceElement: StackTraceElement?,
    @JvmField // todo lazy { }, not a JvmField
    public val spilledVariables: Array<String>?
) : CoroutineStackFrame {
    override fun getStackTraceElement(): StackTraceElement? = stackTraceElement
}
