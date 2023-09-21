/*
 * Copyright 2016-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * Thrown when multiply exception were thrown in event loop.
 * @see runEventLoop
 */
public class EventLoopException(public val causes: List<Throwable>) : Throwable("Multiple exceptions were thrown in the event loop.")