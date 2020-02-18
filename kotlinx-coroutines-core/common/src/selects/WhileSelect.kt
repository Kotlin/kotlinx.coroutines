/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*

/**
 * Loops while [select] expression returns `true`.
 *
 * The statement of the form:
 *
 * ```
 * whileSelect {
 *     /*body*/
 * }
 * ```
 *
 * is a shortcut for:
 *
 * ```
 * while(select<Boolean> {
 *    /*body*/
 * }) {}
 *
 * **Note: This is an experimental api.** It may be replaced with a higher-performance DSL for selection from loops.
 */
@ExperimentalCoroutinesApi
public suspend inline fun whileSelect(crossinline builder: SelectBuilder<Boolean>.() -> Unit) {
    while(select<Boolean>(builder)) {}
}
