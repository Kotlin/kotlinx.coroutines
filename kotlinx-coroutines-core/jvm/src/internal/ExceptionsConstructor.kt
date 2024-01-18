package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.lang.reflect.*
import java.util.*
import java.util.concurrent.locks.*
import kotlin.concurrent.*

private val throwableFields = Throwable::class.java.fieldsCountOrDefault(-1)
private typealias Ctor = (Throwable) -> Throwable?

private val ctorCache = try {
    if (ANDROID_DETECTED) WeakMapCtorCache
    else ClassValueCtorCache
} catch (e: Throwable) {
    // Fallback on Java 6 or exotic setups
    WeakMapCtorCache
}

@Suppress("UNCHECKED_CAST")
internal fun <E : Throwable> tryCopyException(exception: E): E? {
    // Fast path for CopyableThrowable
    if (exception is CopyableThrowable<*>) {
        return runCatching { exception.createCopy() as E? }.getOrNull()
    }
    return ctorCache.get(exception.javaClass).invoke(exception) as E?
}

private fun <E : Throwable> createConstructor(clz: Class<E>): Ctor {
    val nullResult: Ctor = { null } // Pre-cache class
    // Skip reflective copy if an exception has additional fields (that are typically populated in user-defined constructors)
    if (throwableFields != clz.fieldsCountOrDefault(0)) return nullResult
    /*
     * Try to reflectively find constructor(message, cause), constructor(message), constructor(cause), or constructor(),
     * in that order of priority.
     * Exceptions are shared among coroutines, so we should copy exception before recovering current stacktrace.
     *
     * By default, Java's reflection iterates over ctors in the source-code order and the sorting is stable, so we can
     * not rely on the order of iteration. Instead, we assign a unique priority to each ctor type.
     */
    return clz.constructors.map { constructor ->
        val p = constructor.parameterTypes
        when (p.size) {
            2 -> when {
                p[0] == String::class.java && p[1] == Throwable::class.java ->
                    safeCtor { e -> constructor.newInstance(e.message, e) as Throwable } to 3
                else -> null to -1
            }
            1 -> when (p[0]) {
                String::class.java ->
                    safeCtor { e -> (constructor.newInstance(e.message) as Throwable).also { it.initCause(e) } } to 2
                Throwable::class.java ->
                    safeCtor { e -> constructor.newInstance(e) as Throwable } to 1
                else -> null to -1
            }
            0 -> safeCtor { e -> (constructor.newInstance() as Throwable).also { it.initCause(e) } } to 0
            else -> null to -1
        }
    }.maxByOrNull(Pair<*, Int>::second)?.first ?: nullResult
}

private fun safeCtor(block: (Throwable) -> Throwable): Ctor = { e ->
    runCatching {
        val result = block(e)
        /*
         * Verify that the new exception has the same message as the original one (bail out if not, see #1631)
         * or if the new message complies the contract from `Throwable(cause).message` contract.
         */
        if (e.message != result.message && result.message != e.toString()) null
        else result
    }.getOrNull()
}

private fun Class<*>.fieldsCountOrDefault(defaultValue: Int) =
    kotlin.runCatching { fieldsCount() }.getOrDefault(defaultValue)

private tailrec fun Class<*>.fieldsCount(accumulator: Int = 0): Int {
    val fieldsCount = declaredFields.count { !Modifier.isStatic(it.modifiers) }
    val totalFields = accumulator + fieldsCount
    val superClass = superclass ?: return totalFields
    return superClass.fieldsCount(totalFields)
}

internal abstract class CtorCache {
    abstract fun get(key: Class<out Throwable>): Ctor
}

private object WeakMapCtorCache : CtorCache() {
    private val cacheLock = ReentrantReadWriteLock()
    private val exceptionCtors: WeakHashMap<Class<out Throwable>, Ctor> = WeakHashMap()

    override fun get(key: Class<out Throwable>): Ctor {
        cacheLock.read { exceptionCtors[key]?.let { return it } }
        cacheLock.write {
            exceptionCtors[key]?.let { return it }
            return createConstructor(key).also { exceptionCtors[key] = it }
        }
    }
}

@IgnoreJreRequirement
private object ClassValueCtorCache : CtorCache() {
    private val cache = object : ClassValue<Ctor>() {
        override fun computeValue(type: Class<*>?): Ctor {
            @Suppress("UNCHECKED_CAST")
            return createConstructor(type as Class<out Throwable>)
        }
    }

    override fun get(key: Class<out Throwable>): Ctor = cache.get(key)
}
