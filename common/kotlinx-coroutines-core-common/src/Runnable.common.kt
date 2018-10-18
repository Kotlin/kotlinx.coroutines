/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 */
public expect interface Runnable {
    public fun run()
}

/**
 * Creates [Runnable] task instance.
 */
@Suppress("FunctionName")
public expect inline fun Runnable(crossinline block: () -> Unit): Runnable