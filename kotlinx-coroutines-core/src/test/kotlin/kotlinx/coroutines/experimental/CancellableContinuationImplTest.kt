/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import org.junit.Test
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.EmptyCoroutineContext
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED

class CancellableContinuationImplTest {
    @Test
    fun testIdempotentSelectResume() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resume(value: String) {
                check(value === "OK")
                resumed = true
            }
            override fun resumeWithException(exception: Throwable) { error("Should not happen") }
        }
        val c = CancellableContinuationImpl<String>(delegate, defaultResumeMode = MODE_CANCELLABLE, active = false)
        check(!c.isSelected)
        check(!c.isActive)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(c.isActive)
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        val token = c.tryResume("OK", "RESUME") ?: error("Failed")
        check(c.isSelected)
        check(!c.isActive)
        check(null == c.tryResume("FAIL"))
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(token === c.tryResume("OK", "RESUME"))
        check(c.getResult() === COROUTINE_SUSPENDED)
        check(!resumed)
        c.completeResume(token)
        check(resumed)
        check(c.isSelected)
        check(!c.isActive)
        check(null == c.tryResume("FAIL"))
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(token === c.tryResume("OK", "RESUME"))
        check(c.getResult() === "OK")
    }

    @Test
    fun testIdempotentSelectCancel() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resume(value: String) { error("Should not happen") }
            override fun resumeWithException(exception: Throwable) {
                check(exception is CancellationException)
                resumed = true
            }
        }
        val c = CancellableContinuationImpl<String>(delegate, defaultResumeMode = MODE_CANCELLABLE, active = false)
        check(!c.isSelected)
        check(!c.isActive)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(c.isActive)
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(c.getResult() === COROUTINE_SUSPENDED)
        check(!resumed)
        c.cancel()
        check(resumed)
        check(c.isSelected)
        check(!c.isActive)
        check(null == c.tryResume("FAIL"))
        check(!c.start())
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(null === c.tryResume("OK", "RESUME"))
    }
}