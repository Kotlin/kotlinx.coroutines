/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.Continuation

// internal debugging tools

internal val Any.hexAddress: String
    get() = Integer.toHexString(System.identityHashCode(this))

internal fun Any?.toSafeString(): String =
    try { toString() }
    catch (e: Throwable) { "toString() failed with $e" }

// **KLUDGE**: there is no reason to include continuation into debug string until the following ticket is resolved:
// KT-18986 Debug-friendly toString implementation for CoroutineImpl
// (the current string representation of continuation is useless and uses buggy reflection internals)
// So, this function is a replacement that extract a usable information from continuation -> its class name, at least
internal actual fun Continuation<*>.toDebugString(): String = when (this) {
    is DispatchedContinuation -> toString()
    else -> "${this::class.java.name}@$hexAddress"
}

