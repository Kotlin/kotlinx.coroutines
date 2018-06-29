/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

import kotlinx.io.pool.*
import org.junit.rules.*
import org.junit.runner.*
import org.junit.runners.model.*
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

class VerifyingObjectPool<T : Any> internal constructor(private val delegate: ObjectPool<T>, private val log: Boolean = false) : ObjectPool<T> by delegate, TestRule {
    private val allocated = ConcurrentHashMap<IdentityWrapper<T>, Boolean>()

    val used: Int
        get() = allocated.size

    override fun borrow(): T {
        if (log) {
            Trace.Allocate().dump()
        }

        val instance = delegate.borrow()
        if (allocated.put(IdentityWrapper(instance), true) != null) {
            throw AssertionError("Instance $instance has been provided by the pool twice")
        }
        return instance
    }

    override fun recycle(instance: T) {
        if (log) {
            Trace.Recycle().dump()
        }

        if (allocated.remove(IdentityWrapper(instance)) == null) {
            throw AssertionError("Instance $instance hasn't been borrowed but tried to recycle (possibly double recycle)")
        }
        delegate.recycle(instance)
    }

    override fun apply(base: Statement, description: Description): Statement {
        return object: Statement() {
            override fun evaluate() {
                var failed = false
                try {
                    base.evaluate()
                } catch (t: Throwable) {
                    failed = true
                    try {
                        assertEmpty()
                    } catch (emptyFailed: Throwable) {
                        throw MultipleFailureException(listOf(t, emptyFailed))
                    }
                    throw t
                } finally {
                    if (!failed) {
                        assertEmpty()
                    }
                }
            }
        }
    }

    private fun assertEmpty() {
        assertEquals(0, allocated.size)
    }

    private class IdentityWrapper<T : Any>(private val instance: T) {
        override fun equals(other: Any?): Boolean {
            if (other !is IdentityWrapper<*>) return false
            return other.instance === this.instance
        }

        override fun hashCode() = System.identityHashCode(instance)
    }

    private sealed class Trace : RuntimeException() {
        class Allocate : Trace()
        class Recycle() : Trace()

        fun dump() {
            val sb = StringWriter()
            val pw = PrintWriter(sb, false)
            printStackTrace(pw)
            pw.close()

            println(sb.buffer)
        }
    }
}
