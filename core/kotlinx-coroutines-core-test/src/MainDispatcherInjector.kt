/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*

/**
 * Object, responsible for injecting custom implementation of [Dispatchers.Main].
 * The main purpose of this class is to override default Main dispatcher in unit tests where main thread is inaccessible.
 * By default, [Dispatchers.Unconfined] is used.
 *
 * If this class is present in the classpath, it **overrides** default [Dispatchers.Main] implementation with its own implementation,
 * making usages of the original [Dispatchers.Main] impossible.
 */
@ExperimentalCoroutinesApi
public object MainDispatcherInjector {

    private val mainDispatcher = (Dispatchers.Main as? InjectableMainDispatcher)
        ?: error("Injectable dispatcher is not found in class path (${Dispatchers.Main} was found instead). " +
                "Please check your META-INF/services and ProGuard settings")

    /**
     * Injects given dispatcher as underlying dispatcher of [Dispatchers.Main].
     * All consecutive usages of [Dispatchers.Main] will use [dispatcher] under the hood, though it's not guaranteed
     * that [Dispatchers.Main] will be equal to given [dispatcher].
     *
     * Note that it is unsafe to call this method from coroutine, launched in [Dispatchers.Main].
     * Such usage may lead to undefined behaviour and [IllegalStateException].
     */
    public fun inject(dispatcher: CoroutineDispatcher) {
        mainDispatcher.inject(dispatcher)
    }

    /**
     * Resets state of [Dispatchers.Main] to [Dispatchers.Unconfined].
     * Used to cleanup all possible dependencies, should be used in tear down (`@After`) methods.
     */
    public fun reset() = inject(Dispatchers.Unconfined)
}
