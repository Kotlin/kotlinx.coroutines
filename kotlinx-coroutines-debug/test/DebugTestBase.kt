/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.debug


import kotlinx.coroutines.*
import kotlinx.coroutines.debug.junit4.*
import org.junit.*

open class DebugTestBase : TestBase() {

    @JvmField
    @Rule
    val timeout = CoroutinesTimeout.seconds(60)

    @Before
    open fun setUp() {
        before()
        DebugProbes.sanitizeStackTraces = false
        DebugProbes.enableCreationStackTraces = true
        DebugProbes.install()
    }

    @After
    fun tearDown() {
        try {
            DebugProbes.uninstall()
        } finally {
            onCompletion()
        }
    }
}
