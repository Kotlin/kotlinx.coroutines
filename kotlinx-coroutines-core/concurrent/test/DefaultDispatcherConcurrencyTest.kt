/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

class DefaultDispatcherConcurrencyTest : AbstractDispatcherConcurrencyTest() {
    override val dispatcher: CoroutineDispatcher = Dispatchers.Default
}
