/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

/**
 * Base class for special [CoroutineDispatcher] which is confined to application "Main" or "UI" thread
 * and used for any UI-based activities. Instance of `MainDispatcher` can be obtained by [Dispatchers.Main].
 *
 * Platform may or may not provide instance of `MainDispatcher`, see documentation to [Dispatchers.Main]
 */
public abstract class MainCoroutineDispatcher : CoroutineDispatcher() {

    /**
     * Returns dispatcher that executes coroutines immediately when it is already in the right context
     * (e.g. current looper is the same as this handler's looper). See [isDispatchNeeded] documentation on
     * why this should not be done by default.
     * Method may throw [UnsupportedOperationException] if immediate dispatching is not supported by current dispatcher,
     * please refer to specific dispatcher documentation.
     *
     * **Note: This is an experimental api.** Semantics of this dispatcher may change in the future.
     */
    @ExperimentalCoroutinesApi
    public abstract val immediate: MainCoroutineDispatcher
}
