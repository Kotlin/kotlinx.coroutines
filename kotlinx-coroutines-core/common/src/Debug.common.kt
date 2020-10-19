/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal expect val DEBUG: Boolean
internal expect val Any.hexAddress: String
internal expect val Any.classSimpleName: String
internal expect fun assert(value: () -> Boolean)

/**
 * Throwable which can be cloned during stacktrace recovery in a class-specific way.
 * For additional information about stacktrace recovery see [STACKTRACE_RECOVERY_PROPERTY_NAME]
 *
 * Example of usage:
 * ```
 * class BadResponseCodeException(val responseCode: Int) : Exception(), CopyableThrowable<BadResponseCodeException> {
 *
 *  override fun createCopy(): BadResponseCodeException {
 *    val result = BadResponseCodeException(responseCode)
 *    result.initCause(this)
 *    return result
 *  }
 * ```
 *
 * Copy mechanism is used only on JVM, but it might be convenient to implement it in common exceptions,
 * so on JVM their stacktraces will be properly recovered.
 */
@ExperimentalCoroutinesApi // Since 1.2.0, no ETA on stability
public interface CopyableThrowable<T> where T : Throwable, T : CopyableThrowable<T> {

    /**
     * Creates a copy of the current instance.
     * For better debuggability, it is recommended to use original exception as [cause][Throwable.cause] of the resulting one.
     * Stacktrace of copied exception will be overwritten by stacktrace recovery machinery by [Throwable.setStackTrace] call.
     * An exception can opt-out of copying by returning `null` from this function.
     */
    public fun createCopy(): T?
}
