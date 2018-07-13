/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

/**
 * Closeable entity.
 * @suppress **Deprecated**
 */
@Deprecated("No replacement, see specific use")
public expect interface Closeable {
    @Deprecated("No replacement, see specific code")
    fun close()
}
