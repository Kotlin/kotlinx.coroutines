/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package ordered.tests

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import org.junit.Test
import org.junit.runner.*
import org.robolectric.*
import org.robolectric.annotation.*
import org.robolectric.shadows.*
import kotlin.test.*


class InitMainDispatcherBeforeRobolectricTestRunner(testClass: Class<*>) : RobolectricTestRunner(testClass) {

    init {
        kotlin.runCatching {
            // touch Main, watch it burn
            GlobalScope.launch(Dispatchers.Main + CoroutineExceptionHandler { _, _ -> }) {  }
        }
    }
}

@Config(manifest = Config.NONE, sdk = [28])
@RunWith(InitMainDispatcherBeforeRobolectricTestRunner::class)
class CustomizedRobolectricTest : TestBase() {
    @Test
    fun testComponent()  {
        // Note that main is not set at all
        val component = TestComponent()
        checkComponent(component)
    }

    @Test
    fun testComponentAfterReset()  {
        // Note that main is not set at all
        val component = TestComponent()
        Dispatchers.setMain(Dispatchers.Unconfined)
        Dispatchers.resetMain()
        checkComponent(component)
    }


    private fun checkComponent(component: TestComponent) {
        val mainLooper = ShadowLooper.getShadowMainLooper()
        mainLooper.pause()
        component.launchSomething()
        assertFalse(component.launchCompleted)
        mainLooper.unPause()
        assertTrue(component.launchCompleted)
    }
}