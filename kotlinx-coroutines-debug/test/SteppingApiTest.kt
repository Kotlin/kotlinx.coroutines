@file:Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import kotlinx.coroutines.debug.internal.*
import org.junit.Test
import kotlin.test.*

/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
class SteppingApiTest : DebugTestBase() {

    @Test
    fun testMultipleCoroutines() = runTest {
        val pos1 = DebugProbesImpl.coroutinesRunningOnCurrentThread
        for (i in 1..10) {
            launch(CoroutineName("Child$i")) {
                val pos2 = DebugProbesImpl.coroutinesRunningOnCurrentThread
                assertFalse(pos1.canRunToCurrentLocation())
                delay(1000)
                assertTrue(pos2.canRunToCurrentLocation())
            }
            assertTrue(pos1.canRunToCurrentLocation())
        }
    }
    
    @Test
    fun testCoroutineWithUnconfinedContex() = runTest {
        val pos1 = DebugProbesImpl.coroutinesRunningOnCurrentThread
        launch(CoroutineName("Parent")) {
            assertFalse(pos1.canRunToCurrentLocation())
            val pos2 = DebugProbesImpl.coroutinesRunningOnCurrentThread
            launch(CoroutineName("Child") + Dispatchers.Unconfined) {
                assertTrue(pos2.canRunToCurrentLocation())
                val pos3 = DebugProbesImpl.coroutinesRunningOnCurrentThread
                delay(1000)
                // Child's continuation was dispatched after resume
                assertFalse(pos2.canRunToCurrentLocation())
                assertTrue(pos3.canRunToCurrentLocation())
            }
            assertTrue(pos2.canRunToCurrentLocation())
        }
        assertTrue(pos1.canRunToCurrentLocation())
    }

    @Test
    fun testUndispatchedCoroutineNoSuspends() = runTest {
        val pos1 = DebugProbesImpl.coroutinesRunningOnCurrentThread
        withContext(Dispatchers.Unconfined) {
            assertTrue(pos1.canRunToCurrentLocation())
            var pos2 = DebugProbesImpl.coroutinesRunningOnCurrentThread
            launch(CoroutineName("Child") + Dispatchers.Unconfined) {
                assertTrue(pos1.canRunToCurrentLocation())
                assertTrue(pos2.canRunToCurrentLocation())
                pos2 = DebugProbesImpl.coroutinesRunningOnCurrentThread
            }
            assertTrue(pos1.canRunToCurrentLocation())
            assertTrue(pos2.canRunToCurrentLocation())
        }
        assertTrue(pos1.canRunToCurrentLocation())
    }
    
   @Test
   fun testSameCoroutine() = runTest {
       System.err.println("1")
       val pos1 = DebugProbesImpl.coroutinesRunningOnCurrentThread
       newSingleThreadContext("xxx").use { 
           withContext(it) {
               assertTrue(pos1.canRunToCurrentLocation())
           }
       }
       assertTrue(pos1.canRunToCurrentLocation())
   }

    @Test
    fun testStepIntoNonSuspendFunction() = runTest {
        val pos1 = DebugProbesImpl.coroutinesRunningOnCurrentThread
        coroutineScope { 
            delay(1000)
            assertTrue(pos1.canRunToCurrentLocation())
            for (i in 1 .. 10) {
                launch(CoroutineName("Child_$i") + Dispatchers.Default) {
                    delay(1000)
                    assertFalse(pos1.canRunToCurrentLocation())
                    val pos2 = DebugProbesImpl.coroutinesRunningOnCurrentThread
                    bar(pos2)
                }   
            }
        }
    }
    
    private fun bar(pos: DebugProbesImpl.CoroutinesOnThread) {
        assertTrue(pos.canRunToCurrentLocation())
    }
}
