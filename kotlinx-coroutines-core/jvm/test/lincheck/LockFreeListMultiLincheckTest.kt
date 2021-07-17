/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.lincheck

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*
import kotlin.test.*

@Param.Params(
    Param(name = "id", gen = IntGen::class, conf = "0:1"),
    Param(name = "value", gen = IntGen::class, conf = "1:5")
)
class LockFreeList2LincheckTest : LockFreeListMultiLincheckTest(2)

@Param.Params(
    Param(name = "id", gen = IntGen::class, conf = "0:2"),
    Param(name = "value", gen = IntGen::class, conf = "1:5")
)
class LockFreeList3LincheckTest : LockFreeListMultiLincheckTest(3)

/**
 * Test atomic operations across multiple instances of `LockFreeLinkedList`.
 */
abstract class LockFreeListMultiLincheckTest(val n: Int) : AbstractLincheckTest() {
    private val _opSequence = atomic(0L)

    class Node(val value: Int): LockFreeLinkedListNode() {
        override fun toString(): String = "N$value"
    }
    private val q = Array(n) { index ->
        object : LockFreeLinkedListHead() {
            override fun toString(): String = "H$index"
        }
    }

    @Operation
    fun addLast(@Param(name = "id") id: Int, @Param(name = "value") value: Int) {
        q[id].addLast(Node(value))
    }

    @Operation
    fun addTwo(@Param(name = "id") id: Int, @Param(name = "value") value: Int) {
        var result: Any?
        do {
            val add1 = q[id].describeAddLast(Node(value))
            val add2 = q[(id + 1) % n].describeAddLast(Node(value))
            val op = object : AtomicOp<Any?>() {
                override val opSequence = _opSequence.incrementAndGet()
                init {
                    add1.atomicOp = this
                    add2.atomicOp = this
                }
                override fun prepare(affected: Any?): Any? =
                    add1.prepare(this) ?:
                    add2.prepare(this)

                override fun complete(affected: Any?, failure: Any?) {
                    add1.complete(this, failure)
                    add2.complete(this, failure)
                }
                override fun toString(): String = "AddTwoOp($id, $value)"
            }
            result = op.perform(null)
        } while (result === RETRY_ATOMIC)
        assertNull(result)
    }

    @Operation
    fun removeFirst(@Param(name = "id") id: Int): Int? {
        val node = q[id].removeFirstOrNull() ?: return null
        return (node as Node).value
    }

    fun removeTwo(@Param(name = "id") id: Int): Pair<Int, Int>? {
        var remove1: LockFreeLinkedListNode.RemoveFirstDesc<*>
        var remove2: LockFreeLinkedListNode.RemoveFirstDesc<*>
        var result: Any?
        do {
            remove1 = q[id].describeRemoveFirst()
            remove2 = q[(id + 1) % n].describeRemoveFirst()
            val op = object : AtomicOp<Any?>() {
                override val opSequence = _opSequence.incrementAndGet()
                init {
                    remove1.atomicOp = this
                    remove2.atomicOp = this
                }
                override fun prepare(affected: Any?): Any? =
                    remove1.prepare(this) ?:
                    remove2.prepare(this)

                override fun complete(affected: Any?, failure: Any?) {
                    remove1.complete(this, failure)
                    remove2.complete(this, failure)
                }
                override fun toString(): String = "RemoveTwoOp($id)"
            }
            result = op.perform(null)
        } while (result === RETRY_ATOMIC)
        if (result != null) return null
        return (remove1.result as Node).value to (remove2.result as Node).value
    }

    @OptIn(ExperimentalStdlibApi::class)
    override fun extractState(): List<List<Int>> = q.map {
        buildList { it.forEach<Node> { add(it.value) } }
    }

    @Validate
    fun validate() = q.forEach { it.validate() }

    @StateRepresentation
    fun stateRepresentation() = q.joinToString("; ") { it.stateRepresentation() }

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}