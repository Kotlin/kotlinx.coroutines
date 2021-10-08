/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("TestDispatchers")

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*

@ExperimentalCoroutinesApi
public actual fun Dispatchers.setMain(dispatcher: CoroutineDispatcher) {
    require(dispatcher !is TestMainDispatcher) { "Dispatchers.setMain(Dispatchers.Main) is prohibited, probably Dispatchers.resetMain() should be used instead" }
    val mainDispatcher = Main
    require(mainDispatcher is TestMainDispatcher) { "TestMainDispatcher is not set as main dispatcher, have $mainDispatcher instead." }
    mainDispatcher.setDispatcher(dispatcher)
}

@ExperimentalCoroutinesApi
public actual fun Dispatchers.resetMain() {
    val mainDispatcher = Main
    require(mainDispatcher is TestMainDispatcher) { "TestMainDispatcher is not set as main dispatcher, have $mainDispatcher instead." }
    mainDispatcher.resetDispatcher()
}
