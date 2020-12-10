/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.lincheck

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.paramgen.*
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*

@Param(name = "value", gen = IntGen::class, conf = "1:5")
class LockFreeListLincheckTest : AbstractLincheckTest() {
    class Node(val value: Int): LockFreeLinkedListNode() {
        override fun toString(): String = "N$value"
    }

    private val q: LockFreeLinkedListHead = object : LockFreeLinkedListHead() {
        override fun toString(): String = "H"
    }

    @Operation
    fun addLast(@Param(name = "value") value: Int) {
        q.addLast(Node(value))
    }

    @Operation
    fun addLastIfNotSame(@Param(name = "value") value: Int) {
        q.addLastIfPrev(Node(value)) { !it.isSame(value) }
    }

    @Operation
    fun removeFirst(): Int? {
        val node = q.removeFirstOrNull() ?: return null
        return (node as Node).value
    }

    @Operation
    fun removeFirstOrPeekIfNotSame(@Param(name = "value") value: Int): Int? {
        val node = q.removeFirstIfIsInstanceOfOrPeekIf<Node> { !it.isSame(value) } ?: return null
        return node.value
    }

    private fun Any.isSame(value: Int) = this is Node && this.value == value

    @OptIn(ExperimentalStdlibApi::class)
    override fun extractState(): List<Int> = buildList {
        q.forEach<Node> { add(it.value) }
    }

    @Validate
    fun validate() = q.validate()

    @StateRepresentation
    fun stateRepresentation() = q.stateRepresentation()

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}