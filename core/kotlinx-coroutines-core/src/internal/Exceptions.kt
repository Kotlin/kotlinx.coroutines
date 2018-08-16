/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.coroutines.experimental.*

@Suppress("UNCHECKED_CAST")
internal actual fun <E : Throwable> augmentException(e: E): E {
    if (e is CancellationException) {
        return e
    }

    try {
        for (constructor in e.javaClass.constructors) {
            val parameters = constructor.parameterTypes
            if (parameters.isEmpty()) {
                return (constructor.newInstance() as E).also { it.initCause(e) }
            } else if (parameters.size == 1 && parameters[0] == Throwable::class.java) {
                return constructor.newInstance(e) as E
            } else if (parameters.size == 2 && parameters[0] == String::class.java && parameters[1] == Throwable::class.java) {
                return constructor.newInstance(e.message, e) as E
            }
        }
    } catch (e: Exception) {
        // Do nothing
    }
    return e
}
