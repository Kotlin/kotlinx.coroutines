/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.internal.*
import kotlin.jvm.*
import kotlin.native.concurrent.*

/**
 * This value is used a a surrogate `null` value when needed.
 * It should never leak to the outside world.
 */
@JvmField
@SharedImmutable
internal val NULL = Symbol("NULL")

/*
 * Symbol used to indicate that the flow is complete.
 * It should never leak to the outside world.
 */
@JvmField
@SharedImmutable
internal val DONE = Symbol("DONE")
