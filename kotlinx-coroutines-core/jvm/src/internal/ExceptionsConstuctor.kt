/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.lang.reflect.*
import java.util.*
import java.util.concurrent.locks.*
import kotlin.concurrent.*

private val throwableFields = Throwable::class.java.fieldsCountOrDefault(-1)
private val cacheLock = ReentrantReadWriteLock()
// Replace it with ClassValue when Java 6 support is over
private val exceptionConstructors: WeakHashMap<Class<out Throwable>, (Throwable) -> Throwable?> = WeakHashMap()

@Suppress("UNCHECKED_CAST")
internal fun <E : Throwable> tryCopyException(exception: E): E? {
    if (exception is CopyableThrowable<*>) {
        return runCatching { exception.createCopy() as E }.getOrNull()
    }

    val cachedCtor = cacheLock.read {
        exceptionConstructors[exception.javaClass]
    }

    if (cachedCtor != null) return cachedCtor(exception) as E?
    /*
     * Skip reflective copy if an exception has additional fields (that are usually populated in user-defined constructors)
     */
    if (throwableFields != exception.javaClass.fieldsCountOrDefault(0)) {
        cacheLock.write { exceptionConstructors[exception.javaClass] = { null } }
        return null
    }

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

private fun Class<*>.fieldsCountOrDefault(defaultValue: Int) = kotlin.runCatching { fieldsCount() }.getOrDefault(defaultValue)

private tailrec fun Class<*>.fieldsCount(accumulator: Int = 0): Int {
    val fieldsCount = declaredFields.count { !Modifier.isStatic(it.modifiers) }
    val totalFields = accumulator + fieldsCount
    val superClass = superclass ?: return totalFields
    return superClass.fieldsCount(totalFields)
}