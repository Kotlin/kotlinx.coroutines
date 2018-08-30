/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class CurrentScopeTest : TestBase() {

    @Test
    fun testScope() = runTest {
        suspend fun callJobScoped() = currentScope {
            launch {
                finish(3)
            }
        }


        expect(1)
        callJobScoped()
        expect(2)
    }

    @Test
    fun testNestedScope() = runTest {
        suspend fun callJobScoped() = currentScope {
            launch {
                expect(2)
            }
        }

        expect(1)
        coroutineScope {
            callJobScoped()
        }

        finish(3)
    }

    @Test
    fun testThrowException() = runTest(expected = { it is IndexOutOfBoundsException }) {
        suspend fun callJobScoped() = currentScope {
            launch {
                finish(3)
                throw IndexOutOfBoundsException()
            }
        }

        expect(1)
        callJobScoped()
        expect(2)
    }
}
