/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*

@ExperimentalCoroutinesApi
public actual fun Dispatchers.setMain(dispatcher: CoroutineDispatcher) {
    throw UnsupportedOperationException("`setMain` is not supported on Native")
}

@ExperimentalCoroutinesApi
public actual fun Dispatchers.resetMain() {
    throw UnsupportedOperationException("`resetMain` is not supported on Native")
}