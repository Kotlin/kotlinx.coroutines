/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.test

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.DefaultExecutor
import kotlinx.coroutines.experimental.hexAddress
import kotlin.coroutines.experimental.CoroutineContext

public object Tests {

    // used for tests
    public fun usePrivatePool() {
        CommonPool.usePrivatePool()
    }

    // used for tests
    public fun shutdown(shutdownTimeout: Long) {
        CommonPool.shutdown(shutdownTimeout)
        DefaultExecutor.shutdown(shutdownTimeout)
    }
}

// used for tests
public fun CoroutineContext.defaultToStringTest() = "TestCoroutineContext@$hexAddress"