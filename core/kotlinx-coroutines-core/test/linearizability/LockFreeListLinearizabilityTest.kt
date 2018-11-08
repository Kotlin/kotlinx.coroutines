/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("unused")

package kotlinx.coroutines.linearizability

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.strategy.stress.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.test.*

@Param(name = "value", gen = IntGen::class, conf = "1:3")
class LockFreeListLinearizabilityTest : TestBase() {
    class Node(val value: Int): LockFreeLinkedListNode()

    private val q: LockFreeLinkedListHead = LockFreeLinkedListHead()

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

    @Test
    fun testAddRemoveLinearizability() {
        val options = StressOptions()
            .iterations(100 * stressTestMultiplierSqrt)
            .invocationsPerIteration(1000 * stressTestMultiplierSqrt)
            .threads(3)
        LinChecker.check(LockFreeListLinearizabilityTest::class.java, options)
    }

    private var _curElements: ArrayList<Int>? = null
    private val curElements: ArrayList<Int> get() {
        if (_curElements == null) {
            _curElements = ArrayList()
            q.forEach<Node> { _curElements!!.add(it.value) }
        }
        return _curElements!!
    }

    override fun equals(other: Any?): Boolean {
        other as LockFreeListLinearizabilityTest
        return curElements == other.curElements
    }

    override fun hashCode(): Int {
        return curElements.hashCode()
    }
}