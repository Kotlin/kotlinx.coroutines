/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class CacheTest : TestBase() {

    @Test
    fun illegalHistorySizes_throwException() = runTest {

        assertFailsWith<IllegalArgumentException> { flowOf("a").cache(-3) }
        assertFailsWith<IllegalArgumentException> { flowOf("a").cache(-2) }
        assertFailsWith<IllegalArgumentException> { flowOf("a").cache(-1) }
        assertFailsWith<IllegalArgumentException> { flowOf("a").cache(0) }
    }

    @Test
    fun firstCollection_doesNotEmitCache() = runTest {

        val list = listOf(1, 2, 3, 4, 5)

        val flow = list.asFlow().cache(2)

        val collected = flow.toList()

        assertEquals(list, collected)
    }

    @Test
    fun secondCollection_receivesCacheFirst() = runTest {

        val list = listOf(1, 2, 3, 4, 5)

        val flow = list.asFlow().cache(2)

        flow.collect() // collect [1, 2, 3, 4, 5], cache = [4, 5]

        val collect2 = flow.toList()

        assertEquals(listOf(4, 5, 1, 2, 3, 4, 5), collect2)
    }

    @Test
    fun thirdCollection_getsUpdatedCache() = runTest {

        val list = listOf(1, 2, 3, 4, 5)

        val flow = list.asFlow().cache(2)

        flow.take(4).collect() // collect [1, 2, 3, 4], cache = [3, 4]
        flow.take(3).collect() // collect [3, 4, 1], cache = [4, 1]

        val collect3 = flow.toList()

        assertEquals(listOf(4, 1, 1, 2, 3, 4, 5), collect3)
    }

    @Test
    fun largeCache_buildsOverMultipleCollectors() = runTest {

        val list = listOf(1, 2, 3, 4, 5)

        val flow = list.asFlow().cache(8)

        // collect twice to generate the cache
        flow.take(4).collect()    // collect [1, 2, 3, 4], cache = [1, 2, 3, 4]
        flow.collect()                  // collect [1, 2, 3, 4, 1, 2, 3, 4, 5], cache = [2, 3, 4, 1, 2, 3, 4, 5]

        val collect3 = flow.toList()

        val expected = listOf(2, 3, 4, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5)

        assertEquals(expected, collect3)
    }

}
