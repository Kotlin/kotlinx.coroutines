/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.lang.ref.*
import java.lang.reflect.*
import java.text.*
import java.util.*
import java.util.Collections.*
import java.util.concurrent.atomic.*
import java.util.concurrent.locks.*
import kotlin.test.*

object FieldWalker {
    sealed class Ref {
        object RootRef : Ref()
        class FieldRef(val parent: Any, val name: String) : Ref()
        class ArrayRef(val parent: Any, val index: Int) : Ref()
    }

    private val fieldsCache = HashMap<Class<*>, List<Field>>()

    init {
        // excluded/terminal classes (don't walk them)
        fieldsCache += listOf(
            Any::class, String::class, Thread::class, Throwable::class, StackTraceElement::class,
            WeakReference::class, ReferenceQueue::class, AbstractMap::class,
            ReentrantReadWriteLock::class, SimpleDateFormat::class
        )
            .map { it.java }
            .associateWith { emptyList<Field>() }
    }

    /*
     * Reflectively starts to walk through object graph and returns identity set of all reachable objects.
     * Use [walkRefs] if you need a path from root for debugging.
     */
    public fun walk(root: Any?): Set<Any> = walkRefs(root, false).keys

    public fun assertReachableCount(expected: Int, root: Any?, rootStatics: Boolean = false, predicate: (Any) -> Boolean) {
        val visited = walkRefs(root, rootStatics)
        val actual = visited.keys.filter(predicate)
        if (actual.size != expected) {
            val textDump = actual.joinToString("") { "\n\t" + showPath(it, visited) }
            assertEquals(
                expected, actual.size,
                "Unexpected number objects. Expected $expected, found ${actual.size}$textDump"
            )
        }
    }

    /*
     * Reflectively starts to walk through object graph and map to all the reached object to their path
     * in from root. Use [showPath] do display a path if needed.
     */
    private fun walkRefs(root: Any?, rootStatics: Boolean): IdentityHashMap<Any, Ref> {
        val visited = IdentityHashMap<Any, Ref>()
        if (root == null) return visited
        visited[root] = Ref.RootRef
        val stack = ArrayDeque<Any>()
        stack.addLast(root)
        var statics = rootStatics
        while (stack.isNotEmpty()) {
            val element = stack.removeLast()
            try {
                visit(element, visited, stack, statics)
                statics = false // only scan root static when asked
            } catch (e: Exception) {
                error("Failed to visit element ${showPath(element, visited)}: $e")
            }
        }
        return visited
    }

    private fun showPath(element: Any, visited: Map<Any, Ref>): String {
        val path = ArrayList<String>()
        var cur = element
        while (true) {
            val ref = visited.getValue(cur)
            if (ref is Ref.RootRef) break
            when (ref) {
                is Ref.FieldRef -> {
                    cur = ref.parent
                    path += "|${ref.parent.javaClass.simpleName}::${ref.name}"
                }
                is Ref.ArrayRef -> {
                    cur = ref.parent
                    path += "[${ref.index}]"
                }
            }
        }
        path.reverse()
        return path.joinToString("")
    }

    private fun visit(element: Any, visited: IdentityHashMap<Any, Ref>, stack: ArrayDeque<Any>, statics: Boolean) {
        val type = element.javaClass
        when {
            // Special code for arrays
            type.isArray && !type.componentType.isPrimitive -> {
                @Suppress("UNCHECKED_CAST")
                val array = element as Array<Any?>
                array.forEachIndexed { index, value ->
                    push(value, visited, stack) { Ref.ArrayRef(element, index) }
                }
            }
            // Special code for platform types that cannot be reflectively accessed on modern JDKs
            type.name.startsWith("java.") && element is Collection<*> -> {
                element.forEachIndexed { index, value ->
                    push(value, visited, stack) { Ref.ArrayRef(element, index) }
                }
            }
            type.name.startsWith("java.") && element is Map<*, *> -> {
                push(element.keys, visited, stack) { Ref.FieldRef(element, "keys") }
                push(element.values, visited, stack) { Ref.FieldRef(element, "values") }
            }
            element is AtomicReference<*> -> {
                push(element.get(), visited, stack) { Ref.FieldRef(element, "value") }
            }
            element is AtomicReferenceArray<*> -> {
                for (index in 0 until element.length()) {
                    push(element[index], visited, stack) { Ref.ArrayRef(element, index) }
                }
            }
            element is AtomicLongFieldUpdater<*> -> {
                /* filter it out here to suppress its subclasses too */
            }
            // All the other classes are reflectively scanned
            else -> fields(type, statics).forEach { field ->
                push(field.get(element), visited, stack) { Ref.FieldRef(element, field.name) }
                // special case to scan Throwable cause (cannot get it reflectively)
                if (element is Throwable) {
                    push(element.cause, visited, stack) { Ref.FieldRef(element, "cause") }
                }
            }
        }
    }

    private inline fun push(value: Any?, visited: IdentityHashMap<Any, Ref>, stack: ArrayDeque<Any>, ref: () -> Ref) {
        if (value != null && !visited.containsKey(value)) {
            visited[value] = ref()
            stack.addLast(value)
        }
    }

    private fun fields(type0: Class<*>, rootStatics: Boolean): List<Field> {
        fieldsCache[type0]?.let { return it }
        val result = ArrayList<Field>()
        var type = type0
        var statics = rootStatics
        while (true) {
            val fields = type.declaredFields.filter {
                !it.type.isPrimitive
                    && (statics || !Modifier.isStatic(it.modifiers))
                    && !(it.type.isArray && it.type.componentType.isPrimitive)
                    && it.name != "previousOut" // System.out from TestBase that we store in a field to restore later
            }
            fields.forEach { it.isAccessible = true } // make them all accessible
            result.addAll(fields)
            type = type.superclass
            statics = false
            val superFields = fieldsCache[type] // will stop at Any anyway
            if (superFields != null) {
                result.addAll(superFields)
                break
            }
        }
        fieldsCache[type0] = result
        return result
    }
}
