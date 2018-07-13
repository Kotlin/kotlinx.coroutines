/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.examples

import java.text.*
import java.util.*

public class Try<out T> private constructor(private val _value: Any?) {
    private class Fail(val exception: Throwable) {
        override fun toString(): String = "Failure[$exception]"
    }
    public companion object {
        public operator fun <T> invoke(block: () -> T): Try<T> =
            try { Success(block()) } catch(e: Throwable) { Failure<T>(e) }
        public fun <T> Success(value: T) = Try<T>(value)
        public fun <T> Failure(exception: Throwable) = Try<T>(Fail(exception))
    }
    @Suppress("UNCHECKED_CAST")
    public val value: T get() = if (_value is Fail) throw _value.exception else _value as T
    public val exception: Throwable? get() = (_value as? Fail)?.exception
    override fun toString(): String = _value.toString()
}

fun log(msg: String) = println("${SimpleDateFormat("yyyyMMdd-HHmmss.sss").format(Date())} [${Thread.currentThread().name}] $msg")
