/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import com.google.common.reflect.*
import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class ListAllCoroutineThrowableSubclassesTest {

    /*
     * These are all known throwables in kotlinx.coroutines.
     * If you have added one, this test will fail to make
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
        "kotlinx.coroutines.DiagnosticCoroutineContextException",
        "kotlinx.coroutines.CoroutinesInternalError",
        "kotlinx.coroutines.channels.ClosedSendChannelException",
        "kotlinx.coroutines.channels.ClosedReceiveChannelException",
        "kotlinx.coroutines.flow.internal.ChildCancelledException",
        "kotlinx.coroutines.flow.internal.AbortFlowException",
        )

    @Test
    fun testThrowableSubclassesAreSerializable() {
        var throwables = 0
        val classes = ClassPath.from(this.javaClass.classLoader)
            .getTopLevelClassesRecursive("kotlinx.coroutines");
        classes.forEach {
            if (Throwable::class.java.isAssignableFrom(it.load())) {
                ++throwables
                // println(""""$it",""")
                assertTrue(knownThrowables.contains(it.toString()))
            }
        }

        assertEquals(knownThrowables.size, throwables)
    }
}
