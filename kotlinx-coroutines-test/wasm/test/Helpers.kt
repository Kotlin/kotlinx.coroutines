/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlin.test.*
import kotlin.js.*

actual fun testResultMap(block: (() -> Unit) -> Unit, test: () -> TestResult): TestResult =
    test().then(
        {
            block {
            }
            null
        }, {
            block {
                throw it.toThrowableOrNull() ?: error("Unexpected non-Kotlin exception $it")
            }
            null
        })

actual typealias NoJs = Ignore
