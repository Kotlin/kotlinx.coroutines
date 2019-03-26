/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.junit4.*
import org.junit.*

@Ignore // do not run it on CI
class TestRuleExample {

    @JvmField
    @Rule
    public val timeout = CoroutinesTimeout.seconds(1)

    private suspend fun someFunctionDeepInTheStack() {
        withContext(Dispatchers.IO) {
            delay(Long.MAX_VALUE)
            println("This line is never executed")
        }

        println("This line is never executed as well")
    }

    @Test
    fun hangingTest() = runBlocking {
        val job = launch {
            someFunctionDeepInTheStack()
        }

        println("Doing some work...")
        job.join()
    }

    @Test
    fun successfulTest() = runBlocking {
        launch {
            delay(10)
        }.join()
    }

}
