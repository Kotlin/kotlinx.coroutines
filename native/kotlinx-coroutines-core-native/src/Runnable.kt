/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 */
public actual interface Runnable {
    public actual fun run()
}

@Suppress("FunctionName")
public actual inline fun Runnable(crossinline block: () -> Unit): Runnable =
    object : Runnable {
        override fun run() {
            block()
        }
    }
