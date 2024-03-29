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
    while(select(builder)) { /* do nothing */ }
}
