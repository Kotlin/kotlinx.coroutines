/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import com.google.common.reflect.*
import kotlinx.coroutines.*
import org.junit.Test
import java.io.Serializable
import java.lang.reflect.Modifier
import kotlin.test.*

class ListAllCoroutineThrowableSubclassesTest {

    /*
     * These are all the known throwables in kotlinx.coroutines.
     * If you add one, this test will fail to make
     * you ensure your exception type is java.io.Serializable.
     *
     * We do not have means to check it automatically, so checks are delegated to humans.
     *
     * See #3328 for serialization rationale.
     */
    private val knownThrowables = setOf(
        "kotlinx.coroutines.TimeoutCancellationException",
        "kotlinx.coroutines.JobCancellationException",
        "kotlinx.coroutines.internal.UndeliveredElementException",
        "kotlinx.coroutines.CompletionHandlerException",
        "kotlinx.coroutines.internal.DiagnosticCoroutineContextException",
        "kotlinx.coroutines.internal.ExceptionSuccessfullyProcessed",
        "kotlinx.coroutines.CoroutinesInternalError",
        "kotlinx.coroutines.channels.ClosedSendChannelException",
        "kotlinx.coroutines.channels.ClosedReceiveChannelException",
        "kotlinx.coroutines.flow.internal.ChildCancelledException",
        "kotlinx.coroutines.flow.internal.AbortFlowException",
    )

    @Test
    fun testThrowableSubclassesAreSerializable() {
        val classes = ClassPath.from(this.javaClass.classLoader)
            .getTopLevelClassesRecursive("kotlinx.coroutines");
        val throwables = classes.filter { Throwable::class.java.isAssignableFrom(it.load()) }.map { it.toString() }
        for (throwable in throwables) {
            for (field in throwable.javaClass.declaredFields) {
                if (Modifier.isStatic(field.modifiers)) continue
                val type = field.type
                assertTrue(type.isPrimitive || Serializable::class.java.isAssignableFrom(type),
                    "Throwable $throwable has non-serializable field $field")
            }
        }
        assertEquals(knownThrowables.sorted(), throwables.sorted())
    }
}
