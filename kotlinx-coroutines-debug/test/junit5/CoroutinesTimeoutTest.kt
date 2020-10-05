/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package junit5
import kotlinx.coroutines.debug.junit5.*
import org.junit.jupiter.api.*

@CoroutinesTimeout(6)
class CoroutinesTimeoutTest {

    @CoroutinesTimeout(5)
    @Test
    fun test() {

    }

    @Test
    fun test2() {

    }
}
