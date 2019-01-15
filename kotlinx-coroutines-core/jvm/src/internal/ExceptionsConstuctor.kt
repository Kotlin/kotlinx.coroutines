/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import java.util.*
import java.util.concurrent.locks.*
import kotlin.concurrent.*

private val cacheLock = ReentrantReadWriteLock()
// Replace it with ClassValue when Java 6 support is over
private val exceptionConstructors: WeakHashMap<Class<out Throwable>, (Throwable) -> Throwable?> = WeakHashMap()

@Suppress("UNCHECKED_CAST")
internal fun <E : Throwable> tryCopyException(exception: E): E? {
    val cachedCtor = cacheLock.read {
        exceptionConstructors[exception.javaClass]
    }

    if (cachedCtor != null) return cachedCtor(exception) as E?

    /*
     * Try to reflectively find constructor(), constructor(message, cause) or constructor(cause).
     * Exceptions are shared among coroutines, so we should copy exception before recovering current stacktrace.
     */
    var ctor: ((Throwable) -> Throwable?)? = null
    val constructors = exception.javaClass.constructors.sortedByDescending { it.parameterTypes.size }
    for (constructor in constructors) {
        val parameters = constructor.parameterTypes
        if (parameters.size == 2 && parameters[0] == String::class.java && parameters[1] == Throwable::class.java) {
            ctor = { e -> runCatching { constructor.newInstance(e.message, e) as E }.getOrNull() }
            break
        } else if (parameters.size == 1 && parameters[0] == Throwable::class.java) {
            ctor = { e -> runCatching { constructor.newInstance(e) as E }.getOrNull() }
            break
        } else if (parameters.isEmpty()) {
            ctor = { e -> runCatching { (constructor.newInstance() as E).also { it.initCause(e) } }.getOrNull() }
            break
        }
    }

    cacheLock.write { exceptionConstructors[exception.javaClass] = (ctor ?: { null }) }
    return ctor?.invoke(exception) as E?
}
