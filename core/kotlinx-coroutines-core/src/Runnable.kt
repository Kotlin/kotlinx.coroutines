/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * A runnable task for [CoroutineDispatcher.dispatch].
 * @suppress
 */
public actual typealias Runnable = java.lang.Runnable

/**
 * Creates [Runnable] task instance.
 */
@Suppress("FunctionName")
public actual inline fun Runnable(crossinline block: () -> Unit): Runnable =
    java.lang.Runnable { block() }
