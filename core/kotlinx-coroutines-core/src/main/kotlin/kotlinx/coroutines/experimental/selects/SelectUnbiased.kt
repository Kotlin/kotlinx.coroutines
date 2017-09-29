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

package kotlinx.coroutines.experimental.selects

import java.util.*
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

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
public inline suspend fun <R> selectUnbiased(crossinline builder: SelectBuilder<R>.() -> Unit): R =
    suspendCoroutineOrReturn { cont ->
        val scope = UnbiasedSelectBuilderImpl(cont)
        try {
            builder(scope)
        } catch (e: Throwable) {
            scope.handleBuilderException(e)
        }
        scope.initSelectResult()
    }


@PublishedApi
internal class UnbiasedSelectBuilderImpl<in R>(cont: Continuation<R>) : SelectBuilder<R> {
    val instance = SelectBuilderImpl(cont)
    val clauses = arrayListOf<() -> Unit>()

    @PublishedApi
    internal fun handleBuilderException(e: Throwable) = instance.handleBuilderException(e)

    @PublishedApi
    internal fun initSelectResult(): Any? {
        if (!instance.isSelected) {
            try {
                Collections.shuffle(clauses)
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