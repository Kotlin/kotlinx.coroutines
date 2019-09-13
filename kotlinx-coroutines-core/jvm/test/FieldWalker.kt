/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.lang.reflect.*
import java.util.*
import java.util.Collections.*

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

            var superclass = type.superclass
            while (superclass != Any::class.java && superclass != null) {
                superclass.visit(element, result, stack)
                superclass = superclass.superclass
            }
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

    private fun Class<*>.fields() = declaredFields.filter {
        !it.type.isPrimitive
                && !Modifier.isStatic(it.modifiers)
                && !(it.type.isArray && it.type.componentType.isPrimitive)
    }
}
