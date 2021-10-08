/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("TestDispatchers")

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*
import kotlin.jvm.*

/**
 * Sets the given [dispatcher] as an underlying dispatcher of [Dispatchers.Main].
 * All subsequent usages of [Dispatchers.Main] will use given [dispatcher] under the hood.
 *
 * It is unsafe to call this method if alive coroutines launched in [Dispatchers.Main] exist.
 */
@ExperimentalCoroutinesApi
public fun Dispatchers.setMain(dispatcher: CoroutineDispatcher) {
    require(dispatcher !is TestMainDispatcher) { "Dispatchers.setMain(Dispatchers.Main) is prohibited, probably Dispatchers.resetMain() should be used instead" }
    getTestMainDispatcher().setDispatcher(dispatcher)
}

/**
 * Resets state of the [Dispatchers.Main] to the original main dispatcher.
 * For example, in Android Main thread dispatcher will be set as [Dispatchers.Main].
 * Used to clean up all possible dependencies, should be used in tear down (`@After`) methods.
 *
 * It is unsafe to call this method if alive coroutines launched in [Dispatchers.Main] exist.
 */
@ExperimentalCoroutinesApi
public fun Dispatchers.resetMain() {
    getTestMainDispatcher().resetDispatcher()
}
