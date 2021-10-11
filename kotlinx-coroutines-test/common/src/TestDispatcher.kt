/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*

/**
 * A test dispatcher that can interface with a [TestCoroutineScheduler].
 */
public abstract class TestDispatcher: CoroutineDispatcher() {
    /** The scheduler that this dispatcher is linked to. */
    public abstract val scheduler: TestCoroutineScheduler

    /** Notifies the dispatcher that it should process a single event marked with [marker] happening at time [time]. */
    internal abstract fun processEvent(time: Long, marker: Any)
}