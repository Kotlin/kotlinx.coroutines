/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.native.ref.*
import kotlin.native.concurrent.*
import kotlin.native.internal.*
import platform.Foundation.*
import platform.darwin.NSObject
import kotlinx.cinterop.*
import kotlin.test.*

class AutoreleaseLeakTest : TestBase() {
    private val testThread = currentThread()

    @Test
    fun testObjCAutorelease() {
        val weakRef = AtomicReference<WeakReference<NSObject>?>(null)

        runTest {
            withContext(Dispatchers.Default) {
                val job = launch {
                    assertNotEquals(testThread, currentThread())
                    val objcObj = NSObject()
                    weakRef.value = WeakReference(objcObj).freeze()

                    // Emulate an autorelease return value in native code.
                    objc_retainAutoreleaseReturnValue(objcObj.objcPtr())
                }
                job.join()
                GC.collect()
            }

            assertNotNull(weakRef.value)
            assertNull(weakRef.value?.value)
        }
    }
}
