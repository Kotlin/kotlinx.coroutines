/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*

/**
 * A variant of [SupervisorJob] that additionally notifies about child failures via a callback.
 */
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
internal class ReportingSupervisorJob(parent: Job? = null, val onChildCancellation: (Throwable) -> Unit) :
    JobImpl(parent) {
    override fun childCancelled(cause: Throwable): Boolean = onChildCancellation(cause).let { false }
}
