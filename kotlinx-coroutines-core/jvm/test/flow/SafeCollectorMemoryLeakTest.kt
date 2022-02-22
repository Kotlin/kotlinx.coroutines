/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import org.junit.*

class SafeCollectorMemoryLeakTest : TestBase() {
    // custom List.forEach impl to avoid using iterator (FieldWalker cannot scan it)
    private inline fun <T> List<T>.listForEach(action: (T) -> Unit) {
        for (i in indices) action(get(i))
    }

    @Test
    fun testCompletionIsProperlyCleanedUp() = runBlocking {
        val job = flow {
            emit(listOf(239))
            expect(2)
            hang {}
        }.transform { l -> l.listForEach { _ -> emit(42) } }
            .onEach { expect(1) }
            .launchIn(this)
        yield()
        expect(3)
        FieldWalker.assertReachableCount(0, job) { it == 239 }
        job.cancelAndJoin()
        finish(4)
    }

    @Test
    fun testCompletionIsNotCleanedUp() = runBlocking {
        val job = flow {
            emit(listOf(239))
            hang {}
        }.transform { l -> l.listForEach { _ -> emit(42) } }
            .onEach {
                expect(1)
                hang { finish(3) }
            }
            .launchIn(this)
        yield()
        expect(2)
        FieldWalker.assertReachableCount(1, job) { it == 239 }
        job.cancelAndJoin()
    }
}
