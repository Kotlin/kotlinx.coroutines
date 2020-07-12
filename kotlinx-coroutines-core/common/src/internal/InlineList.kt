/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.internal

import kotlinx.coroutines.assert

/*
 * Inline class that represents a mutable list, but does not allocate an underlying storage
 * for zero and one elements.
 * Cannot be parametrized with `List<*>`.
 */
internal inline class InlineList<E>(private val holder: Any? = null) {
    public operator fun plus(element: E): InlineList<E>  {
        assert { element !is List<*> } // Lists are prohibited
        return when (holder) {
            null -> InlineList(element)
            is ArrayList<*> -> {
                (holder as ArrayList<E>).add(element)
                InlineList(holder)
            }
            else -> {
                val list = ArrayList<E>(4)
                list.add(holder as E)
                list.add(element)
                InlineList(list)
            }
        }
    }

    public inline fun forEachReversed(action: (E) -> Unit) {
        when (holder) {
            null -> return
            !is ArrayList<*> -> action(holder as E)
            else -> {
                val list = holder as ArrayList<E>
                for (i in (list.size - 1) downTo 0) {
                    action(list[i])
                }
            }
        }
    }
}
