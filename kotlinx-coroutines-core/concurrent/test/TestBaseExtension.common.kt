/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

expect fun TestBase.runMtTest(
    expected: ((Throwable) -> Boolean)? = null,
    unhandled: List<(Throwable) -> Boolean> = emptyList(),
    block: suspend CoroutineScope.() -> Unit
): TestResult
