/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.test.*

class SelectBuilderImplTest {
    @Test
    fun testIdempotentSelectResumeInline() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resumeWith(result: Result<String>) {
                check(result.getOrNull() == "OK")
                resumed = true
            }
        }
        val c = SelectBuilderImpl(delegate)
        // still running builder
        check(!c.isSelected)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        c.completion.resume("OK")
        check(!resumed) // still running builder, didn't invoke delegate
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(c.getResult() === "OK") // then builder returns
    }

    @Test
    fun testIdempotentSelectResumeSuspended() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resumeWith(result: Result<String>) {
                check(result.getOrNull() == "OK")
                resumed = true
            }
        }
        val c = SelectBuilderImpl(delegate)
        check(c.getResult() === COROUTINE_SUSPENDED) // suspend first
        check(!c.isSelected)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(!resumed)
        c.completion.resume("OK")
        check(resumed)
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
    }

    @Test
    fun testIdempotentSelectResumeWithExceptionInline() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resumeWith(result: Result<String>) {
                check(result.exceptionOrNull() is TestException)
                resumed = true
            }
        }
        val c = SelectBuilderImpl(delegate)
        // still running builder
        check(!c.isSelected)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        c.completion.resumeWithException(TestException())
        check(!resumed) // still running builder, didn't invoke delegate
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        try {
            c.getResult() // the builder should throw exception
            error("Failed")
        } catch (e: Throwable) {
            check(e is TestException)
        }
    }

    @Test
    fun testIdempotentSelectResumeWithExceptionSuspended() {
        var resumed = false
        val delegate = object : Continuation<String> {
            override val context: CoroutineContext get() = EmptyCoroutineContext
            override fun resumeWith(result: Result<String>) {
                check(result.exceptionOrNull() is TestException)
                resumed = true
            }
        }
        val c = SelectBuilderImpl(delegate)
        check(c.getResult() === COROUTINE_SUSPENDED) // suspend first
        check(!c.isSelected)
        check(c.trySelect("SELECT"))
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
        check(!resumed)
        c.completion.resumeWithException(TestException())
        check(resumed)
        check(c.isSelected)
        check(!c.trySelect("OTHER"))
        check(c.trySelect("SELECT"))
    }

    class TestException : Throwable()
}