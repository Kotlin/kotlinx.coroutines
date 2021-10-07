/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*

internal class TestMainDispatcherFactory : MainDispatcherFactory {

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher {
        val otherFactories = allFactories.filter { it !== this }
        val secondBestFactory = otherFactories.maxByOrNull { it.loadPriority } ?: MissingMainCoroutineDispatcherFactory
        val dispatcher = secondBestFactory.tryCreateDispatcher(otherFactories)
        return TestMainDispatcher(dispatcher)
    }

    /**
     * [Int.MAX_VALUE] -- test dispatcher always wins no matter what factories are present in the classpath.
     * By default, all actions are delegated to the second-priority dispatcher, so that it won't be the issue.
     */
    override val loadPriority: Int
        get() = Int.MAX_VALUE
}

internal actual fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher {
    val mainDispatcher = Main
    require(mainDispatcher is TestMainDispatcher) { "TestMainDispatcher is not set as main dispatcher, have $mainDispatcher instead." }
    return mainDispatcher
}