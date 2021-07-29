/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * Creates a coroutine execution context using a single thread.
 */
@ExperimentalCoroutinesApi
public expect fun newSingleThreadContext(name: String): SingleThreadDispatcher

/**
 * A coroutine dispatcher that is confined to a single thread.
 */
@ExperimentalCoroutinesApi
public expect abstract class SingleThreadDispatcher : CoroutineDispatcher {
    /**
     * Closes this coroutine dispatcher and shuts down its thread.
     */
    @ExperimentalCoroutinesApi
    public abstract fun close()
}