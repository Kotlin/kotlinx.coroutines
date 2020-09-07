/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class GroupTest : TestBase() {
    @Test
    fun testGroupRunsBlock() = runTest {
        expect(1)
        val group = newGroup<String, String>()
        val expected = "test"
        val deferred = group.runBlock("test") {
            expect(2)
            expected
        }
        val result = deferred.await()
        finish(3)
        assertEquals(result, result)
    }

    @Test
    fun testGroupRunDoesNotRunSecondBlockIfFirstActive() = runTest {
        expect(1)
        val group = newGroup<String, String>()
        val expected = "testReturn"
        val key = "test"
        val deferred = group.runBlock(key) {
            expect(3)
            delay(10)
            expect(4)
            expected
        }
        val secondDeferred = group.runBlock(key) {
            expectUnreached()
            expected
        }
        expect(2)

        coroutineScope {
            launch {
                val result = deferred.await()
                assertEquals(expected, result)
                expect(5)
            }

            launch {
                val result = secondDeferred.await()
                assertEquals(expected, result)
                expect(6)
            }
        }

        finish(7)
    }

    @Test
    fun testGroupRunsSecondBlockIfFirstInactive() = runTest {
        expect(1)
        val group = newGroup<String, String>()
        val expected = "testReturn"
        val key = "test"
        var deferred = group.runBlock(key) {
            expect(3)
            expected
        }
        expect(2)
        var result = deferred.await()
        assertEquals(expected, result)

        deferred = group.runBlock(key) {
            expect(5)
            expected
        }
        expect(4)
        result = deferred.await()
        expect(6)
        assertEquals(expected, result)

        finish(7)
    }

    @Test
    fun testGroupRunsSecondBlockIfFirstActiveAndKeyForgotten() = runTest {
        expect(1)
        val group = newGroup<String, String>()
        val expected = "testReturn"
        val key = "test"
        group.forgetKey(key)

        val deferred = group.runBlock(key) {
            expect(3)
            delay(10)
            expect(6)
            expected
        }
        val secondDeferred = group.runBlock(key) {
            expect(4)
            expected
        }
        expect(2)

        coroutineScope {
            launch {
                val result = deferred.await()
                assertEquals(expected, result)
                expect(7)
            }

            launch {
                val result = secondDeferred.await()
                assertEquals(expected, result)
                expect(5)
            }
        }

        finish(8)
    }
}