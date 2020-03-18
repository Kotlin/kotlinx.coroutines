/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import java.lang.ThreadLocal

@Suppress("ACTUAL_WITHOUT_EXPECT") // internal visibility
internal actual typealias CommonThreadLocal<T> = ThreadLocal<T>
