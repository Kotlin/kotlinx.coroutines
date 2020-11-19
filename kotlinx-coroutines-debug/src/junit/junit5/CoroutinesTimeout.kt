/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit5
import org.junit.jupiter.api.extension.*
import java.lang.annotation.*

/**
 */
@MustBeDocumented
@Retention(value = AnnotationRetention.RUNTIME)
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION)
@ExtendWith(CoroutinesTimeoutExtension::class)
@Inherited
public annotation class CoroutinesTimeout(
    val testTimeoutMs: Long,
    val cancelOnTimeout: Boolean = false
)