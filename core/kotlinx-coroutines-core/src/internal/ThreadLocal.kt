/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import java.lang.ThreadLocal

internal actual typealias CommonThreadLocal<T> = ThreadLocalWithInitialValue<T>

internal class ThreadLocalWithInitialValue<T>(private val supplier: () -> T) : ThreadLocal<T>() {
    override fun initialValue(): T = supplier()
}
