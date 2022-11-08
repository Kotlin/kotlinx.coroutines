/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*


class NoParamAssertionsTest : TestBase() {
    // These tests verify that we haven't omitted "-Xno-param-assertions" and "-Xno-receiver-assertions"

    @Test
    fun testNoReceiverAssertion() {
        val function: (ThreadLocal<Int>, Int) -> ThreadContextElement<Int> = ThreadLocal<Int>::asContextElement
        @Suppress("UNCHECKED_CAST")
        val unsafeCasted = function as ((ThreadLocal<Int>?, Int) -> ThreadContextElement<Int>)
        unsafeCasted(null, 42)
    }

    @Test
    fun testNoParamAssertion() {
        val function: (ThreadLocal<Any>, Any) -> ThreadContextElement<Any> = ThreadLocal<Any>::asContextElement
        @Suppress("UNCHECKED_CAST")
        val unsafeCasted = function as ((ThreadLocal<Any?>?, Any?) -> ThreadContextElement<Any>)
        unsafeCasted(ThreadLocal.withInitial { Any() }, null)
    }
}
