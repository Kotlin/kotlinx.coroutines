/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * Base class for special [CoroutineDispatcher] which is confined to application "Main" or "UI" thread
 * and used for any UI-based activities. Instance of `MainDispatcher` can be obtained by [Dispatchers.Main].
 *
 * Platform may or may not provide instance of `MainDispatcher`, see documentation to [Dispatchers.Main]
 */
public abstract class MainCoroutineDispatcher : CoroutineDispatcher() {

    /**
     * Returns dispatcher that executes coroutines immediately when it is already in the right context
     * (e.g. current looper is the same as this handler's looper) without an additional [re-dispatch][CoroutineDispatcher.dispatch].
     *
     * Immediate dispatcher is safe from stack overflows and in case of nested invocations forms event-loop similar to [Dispatchers.Unconfined].
     * The event loop is an advanced topic and its implications can be found in [Dispatchers.Unconfined] documentation.
     * The formed event-loop is shared with [Unconfined] and other immediate dispatchers, potentially overlapping tasks between them.
     *
     * Example of usage:
     * ```
     * suspend fun updateUiElement(val text: String) {
     *   /*
     *    * If it is known that updateUiElement can be invoked both from the Main thread and from other threads,
     *    * `immediate` dispatcher is used as a performance optimization to avoid unnecessary dispatch.
     *    *
     *    * In that case, when `updateUiElement` is invoked from the Main thread, `uiElement.text` will be
     *    * invoked immediately without any dispatching, otherwise, the `Dispatchers.Main` dispatch cycle will be triggered.
     *    */
     *   withContext(Dispatchers.Main.immediate) {
     *     uiElement.text = text
     *   }
     *   // Do context-independent logic such as logging
     * }
     * ```
     *
     * Method may throw [UnsupportedOperationException] if immediate dispatching is not supported by current dispatcher,
     * please refer to specific dispatcher documentation.
     *
     * [Dispatchers.Main] supports immediate execution for Android, JavaFx and Swing platforms.
     */
    public abstract val immediate: MainCoroutineDispatcher
}
