/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * A coroutine dispatcher that is not confined to any specific thread.
 */
@NativeThreadLocal
internal object Unconfined : CoroutineDispatcher() {
    private data class State(@JvmField var isActive: Boolean = false,
                             @JvmField val threadLocalQueue: ArrayList<Runnable> = ArrayList())
    private val state = CommonThreadLocal { State() }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        // Stack-based event loop on top of thread-local arraylist
        val state = state.get()
        if (state.isActive) {
            state.threadLocalQueue.add(block)
            return
        }

        try {
            state.isActive = true
            block.run()
            while (!state.threadLocalQueue.isEmpty()) {
                val element = state.threadLocalQueue.removeAt(state.threadLocalQueue.lastIndex)
                element.run()
            }
        } catch (e: Throwable) {
            /*
             * This exception doesn't happen normally, only if user either submitted throwing runnable
             * or if we have a bug in implementation. Anyway, reset state of the dispatcher to the initial.
             */
            state.threadLocalQueue.clear()
            throw DispatchException("Unexpected exception in Unconfined loop, clearing pending tasks", e)
        } finally {
            state.isActive = false
        }
    }
    override fun toString(): String = "Unconfined"
}
