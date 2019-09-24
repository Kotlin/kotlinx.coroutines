/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.lang.reflect.*
import java.util.*
import java.util.Collections.*
import kotlin.collections.ArrayList

object FieldWalker {

    /*
     * Reflectively starts to walk through object graph and returns identity set of all reachable objects.
     */
    public fun walk(root: Any): Set<Any> {
        val result = newSetFromMap<Any>(IdentityHashMap())
        result.add(root)
        val stack = ArrayDeque<Any>()
        stack.addLast(root)
        while (stack.isNotEmpty()) {
            val element = stack.removeLast()
            val type = element.javaClass
            type.visit(element, result, stack)
        }
        return result
    }

    private fun Class<*>.visit(
        element: Any,
        result: MutableSet<Any>,
        stack: ArrayDeque<Any>
    ) {
        val fields = fields()
        fields.forEach {
            it.isAccessible = true
            val value = it.get(element) ?: return@forEach
            if (result.add(value)) {
                stack.addLast(value)
            }
        }

        if (isArray && !componentType.isPrimitive) {
            val array = element as Array<Any?>
            array.filterNotNull().forEach {
                if (result.add(it)) {
                    stack.addLast(it)
                }
            }
        }
    }

    private fun Class<*>.fields(): List<Field> {
        val result = ArrayList<Field>()
        var type = this
        while (type != Any::class.java) {
            val fields = type.declaredFields.filter {
                !it.type.isPrimitive
                        && !Modifier.isStatic(it.modifiers)
                        && !(it.type.isArray && it.type.componentType.isPrimitive)
            }
            result.addAll(fields)
            type = type.superclass
        }

        return result
    }

    // Debugging-only
    @Suppress("UNUSED")
    fun printPath(from: Any, to: Any) {
        val pathNodes = ArrayList<String>()
        val visited = newSetFromMap<Any>(IdentityHashMap())
        visited.add(from)
        if (findPath(from, to, visited, pathNodes)) {
            pathNodes.reverse()
            println(pathNodes.joinToString(" -> ", from.javaClass.simpleName + " -> ", "-> " + to.javaClass.simpleName))
        } else {
            println("Path from $from to $to not found")
        }
    }

    private fun findPath(from: Any, to: Any, visited: MutableSet<Any>, pathNodes: MutableList<String>): Boolean {
        if (from === to) {
            return true
        }

        val type = from.javaClass
        if (type.isArray) {
            if (type.componentType.isPrimitive) return false
            val array = from as Array<Any?>
            array.filterNotNull().forEach {
                if (findPath(it, to, visited, pathNodes)) {
                    return true
                }
            }
            return false
        }

        val fields = type.fields()
        fields.forEach {
            it.isAccessible = true
            val value = it.get(from) ?: return@forEach
            if (!visited.add(value)) return@forEach
            val found = findPath(value, to, visited, pathNodes)
            if (found) {
                pathNodes += from.javaClass.simpleName + ":" + it.name
                return true
            }
        }

        return false
    }
}
