/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

public class Group<T, R> internal constructor(
    private val scope: CoroutineScope,
    private val groupMap: MutableMap<T, Deferred<R>>,
    private val forgottenSet: MutableSet<T>
) {
    public fun runBlock(key: T, block: suspend CoroutineScope.() -> R): Deferred<R> =
        scope.runBlock(key, block)

    private fun CoroutineScope.runBlock(
        key: T,
        block: suspend CoroutineScope.() -> R
    ): Deferred<R> {
        return if (groupMap.containsKey(key) && !forgottenSet.contains(key)) {
            val deferred = groupMap.getValue(key)
            if (deferred.isActive) {
                deferred
            } else {
                async(block = block).also {
                    groupMap[key] = it
                }
            }
        } else {
            async(block = block).also {
                groupMap[key] = it
            }
        }
    }

    public fun forgetKey(key: T) {
        forgottenSet.add(key)
    }
}


public expect fun <T, R> CoroutineScope.newGroup(): Group<T, R>