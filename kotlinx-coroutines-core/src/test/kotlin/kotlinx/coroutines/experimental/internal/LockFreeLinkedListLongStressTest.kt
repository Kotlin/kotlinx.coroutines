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

package kotlinx.coroutines.experimental.internal

import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.concurrent.thread
import kotlin.coroutines.experimental.buildIterator

/**
 * This stress test has 2 threads adding on one side on list, 2 more threads adding on the other,
 * and 6 threads iterating and concurrently removing items. The resulting list that is being
 * stressed is long.
 */
class LockFreeLinkedListLongStressTest {
    data class IntNode(val i: Int) : LockFreeLinkedListNode()
    val list = LockFreeLinkedListHead()

    val threads = mutableListOf<Thread>()
    val nAdded = 10_000_000
    val nAddThreads = 4 // must be power of 2 (!!!)
    val nRemoveThreads = 6
    val removeProbability = 0.2
    val workingAdders = AtomicInteger(nAddThreads)

    fun shallRemove(i: Int) = i and 63 != 42

    @Test
    fun testStress() {
        for (j in 0 until nAddThreads)
            threads += thread(start = false, name = "adder-$j") {
                for (i in j until nAdded step nAddThreads) {
                    list.addLast(IntNode(i))
                }
                println("${Thread.currentThread().name} completed")
                workingAdders.decrementAndGet()
            }
        for (j in 0 until nRemoveThreads)
            threads += thread(start = false, name = "remover-$j") {
                val rnd = Random()
                do {
                    val lastTurn = workingAdders.get() == 0
                    list.forEach<IntNode> { node ->
                        if (shallRemove(node.i) && (lastTurn || rnd.nextDouble() < removeProbability))
                            node.remove()
                    }
                } while (!lastTurn)
                println("${Thread.currentThread().name} completed")
            }
        println("Starting ${threads.size} threads")
        for (thread in threads)
            thread.start()
        println("Joining threads")
        for (thread in threads)
            thread.join()
        // verification
        println("Verify result")
        list.validate()
        val expected = buildIterator {
            for (i in 0 until nAdded)
                if (!shallRemove(i))
                    yield(i)
        }
        list.forEach<IntNode> { node ->
            require(node.i == expected.next())
        }
        require(!expected.hasNext())
    }
}