/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.timeunit.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Waits for the result of multiple suspending functions simultaneously like [select], but in an _unbiased_
 * way when multiple clauses are selectable at the same time.
 *
 * This unbiased implementation of `select` expression randomly shuffles the clauses before checking
 * if they are selectable, thus ensuring that there is no statistical bias to the selection of the first
 * clauses.
 *
 * See [select] function description for all the other details.
 */
public suspend inline fun <R> selectUnbiased(crossinline builder: SelectBuilder<R>.() -> Unit): R =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val scope = UnbiasedSelectBuilderImpl(uCont)
        try {
            builder(scope)
        } catch (e: Throwable) {
            scope.handleBuilderException(e)
        }
        scope.initSelectResult()
    }


@PublishedApi
internal class UnbiasedSelectBuilderImpl<in R>(uCont: Continuation<R>) :
    SelectBuilder<R> {
    val instance = SelectBuilderImpl(uCont)
    val clauses = arrayListOf<() -> Unit>()

    @PublishedApi
    internal fun handleBuilderException(e: Throwable) = instance.handleBuilderException(e)

    @PublishedApi
    internal fun initSelectResult(): Any? {
        if (!instance.isSelected) {
            try {
                clauses.shuffle()
                clauses.forEach { it.invoke() }
            } catch (e: Throwable) {
                instance.handleBuilderException(e)
            }
        }
        return instance.getResult()
    }

    override fun SelectClause0.invoke(block: suspend () -> R) {
        clauses += { registerSelectClause0(instance, block) }
    }

    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) {
        clauses += { registerSelectClause1(instance, block) }
    }

    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) {
        clauses += { registerSelectClause2(instance, param, block) }
    }

    override fun onTimeout(time: Long, unit: TimeUnit, block: suspend () -> R) {
        clauses += { instance.onTimeout(time, unit, block) }
    }
}