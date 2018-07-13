/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import com.devexperts.dxlab.lincheck.Actor
import com.devexperts.dxlab.lincheck.Result
import com.devexperts.dxlab.lincheck.verifier.Verifier
import java.lang.reflect.Method
import java.util.*
import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.coroutines.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.intrinsics.startCoroutineUninterceptedOrReturn

data class OpResult(val name: String, val value: Any?) {
    override fun toString(): String = "$name=$value"
}

private const val CS_STR = "COROUTINE_SUSPENDED"

class LinTesting {
    private val resumed = object : ThreadLocal<ArrayList<OpResult>>() {
        override fun initialValue() = arrayListOf<OpResult>()
    }

    private inline fun wrap(block: () -> Any?): Any? =
        try { repr(block()) }
        catch(e: Throwable) { repr(e) }

    private fun repr(e: Any?): Any? =
        when {
            e === COROUTINE_SUSPENDED -> CS_STR
            e is Throwable -> e.toString()
            else -> e
        }

    fun <T> run(name: String, block: suspend () -> T): List<OpResult> {
        val list = resumed.get()
        list.clear()
        val result = arrayListOf(OpResult(name, wrap {
            block.startCoroutineUninterceptedOrReturn(completion = object : Continuation<Any?> {
                override val context: CoroutineContext
                    get() = EmptyCoroutineContext

                override fun resumeWith(result: kotlin.Result<Any?>) {
                    val value = if (result.isSuccess) result.getOrNull() else result.exceptionOrNull()
                    resumed.get() += OpResult(name, repr(value))
                }
            }
            )
        }))
        result.addAll(list)
        return result
    }
}

class LinVerifier(
    actorsPerThread: List<List<Actor>>, testInstance: Any, resetMethod: Method?
) : Verifier(actorsPerThread, testInstance, resetMethod) {
    private val possibleResultsSet: Set<List<List<Result>>> =
        generateAllLinearizableExecutions(actorsPerThread)
            .asSequence()
            .map { linEx: List<Actor> ->
                val res: List<Result> = executeActors(testInstance, linEx)
                val actorIds = linEx.asSequence().withIndex().associateBy({ it.value}, { it.index })
                actorsPerThread.map { actors -> actors.map { actor -> res[actorIds[actor]!!] } }
            }.toSet()

    override fun verifyResults(results: List<List<Result>>) {
        if (!valid(results)) {
            println("\nNon-linearizable execution:")
            printResults(results)
            println("\nPossible linearizable executions:")
            possibleResultsSet.forEach { possibleResults ->
                printResults(possibleResults)
                println()
            }
            throw AssertionError("Non-linearizable execution detected, see log for details")
        }
    }

    private fun printResults(results: List<List<Result>>) {
        results.forEachIndexed { index, res ->
            println("Thread $index: $res")
        }
        println("Op map: ${results.toOpMap()}")
    }

    private fun valid(results: List<List<Result>>): Boolean =
        (results in possibleResultsSet) || possibleResultsSet.any { matches(results, it) }

    private fun matches(results: List<List<Result>>, possible: List<List<Result>>): Boolean =
        results.toOpMap() == possible.toOpMap()

    private fun List<List<Result>>.toOpMap(): Map<String, List<Any?>> {
        val filtered = flatMap { it }.flatMap { it.resultValue }.filter { it.value != CS_STR }
        return filtered.groupBy({ it.name }, { it.value })
    }

    private fun generateAllLinearizableExecutions(actorsPerThread: List<List<Actor>>): List<List<Actor>> {
        val executions = ArrayList<List<Actor>>()
        generateLinearizableExecutions0(
            executions, actorsPerThread, ArrayList<Actor>(), IntArray(actorsPerThread.size),
            actorsPerThread.sumBy { it.size })
        return executions
    }

    @Suppress("UNCHECKED_CAST")
    private fun generateLinearizableExecutions0(executions: MutableList<List<Actor>>, actorsPerThread: List<List<Actor>>,
                                                currentExecution: ArrayList<Actor>, indexes: IntArray, length: Int) {
        if (currentExecution.size == length) {
            executions.add(currentExecution.clone() as List<Actor>)
            return
        }
        for (i in indexes.indices) {
            val actors = actorsPerThread[i]
            if (indexes[i] == actors.size)
                continue
            currentExecution.add(actors[indexes[i]])
            indexes[i]++
            generateLinearizableExecutions0(executions, actorsPerThread, currentExecution, indexes, length)
            indexes[i]--
            currentExecution.removeAt(currentExecution.size - 1)
        }
    }
}

private val VALUE = Result::class.java.getDeclaredField("value").apply { isAccessible = true }

@Suppress("UNCHECKED_CAST")
private val Result.resultValue: List<OpResult>
    get() = VALUE.get(this) as List<OpResult>
