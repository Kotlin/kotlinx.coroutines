/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

@ExperimentalCoroutinesApi
public expect fun newSingleThreadContext(name: String): CloseableCoroutineDispatcher

@ExperimentalCoroutinesApi
public expect fun newFixedThreadPoolContext(nThreads: Int, name: String): CloseableCoroutineDispatcher
