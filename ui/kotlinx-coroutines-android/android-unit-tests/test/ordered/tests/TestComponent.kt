/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package ordered.tests

import kotlinx.coroutines.*

public class TestComponent {

    private val scope = CoroutineScope(SupervisorJob() + Dispatchers.Main)
    public var launchCompleted: Int = 0

    fun doSomething() {
        scope.launch {
            launchCompleted = 1
        }
    }
}
