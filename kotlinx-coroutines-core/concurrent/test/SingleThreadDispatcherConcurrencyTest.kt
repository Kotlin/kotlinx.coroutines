package kotlinx.coroutines

import kotlin.test.*

/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

class SingleThreadDispatcherConcurrencyTest : AbstractDispatcherConcurrencyTest() {
    override val dispatcher: CoroutineDispatcher = newSingleThreadContext("SingleThreadDispatcherConcurrencyTest")

    @AfterTest
    fun shutDown() = (dispatcher as SingleThreadDispatcher).close()
}
