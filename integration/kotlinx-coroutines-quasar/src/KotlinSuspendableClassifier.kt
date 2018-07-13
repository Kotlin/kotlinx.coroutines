/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.quasar

import co.paralleluniverse.fibers.instrument.MethodDatabase
import co.paralleluniverse.fibers.instrument.SuspendableClassifier

/**
 * @suppress **Internal implementation**.
 */
class KotlinSuspendableClassifier : SuspendableClassifier {
    override fun isSuspendable(
            db: MethodDatabase,
            sourceName: String?,
            sourceDebugInfo: String?,
            isInterface: Boolean,
            className: String?,
            superClassName: String?,
            interfaces: Array<out String>,
            methodName: String,
            methodDesc: String,
            methodSignature: String?,
            methodExceptions: Array<out String>?
    ): MethodDatabase.SuspendableType? {
        if (methodName == "run" &&
            methodDesc.startsWith("()") &&
            interfaces.contains("co/paralleluniverse/strands/SuspendableCallable"))
            return MethodDatabase.SuspendableType.SUSPENDABLE
        return null
    }
}