/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.coroutines.internal.*

actual fun TestBase.runMtTest(
    expected: ((Throwable) -> Boolean)?,
    unhandled: List<(Throwable) -> Boolean>,
    block: suspend CoroutineScope.() -> Unit
) {
    if (!multithreadingSupported) return
    return runTest(expected, unhandled, block)
}
