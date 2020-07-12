/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 */
public actual interface Runnable {
    /**
     * @suppress
     */
    public actual fun run()
}

/**
 * Creates [Runnable] task instance.
 */
@Suppress("FunctionName")
public actual inline fun Runnable(crossinline block: () -> Unit): Runnable =
    object : Runnable {
        override fun run() {
            block()
        }
    }
