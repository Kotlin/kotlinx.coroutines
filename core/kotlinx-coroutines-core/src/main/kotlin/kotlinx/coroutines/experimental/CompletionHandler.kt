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

import kotlinx.coroutines.experimental.internal.*

internal actual abstract class CompletionHandlerBase actual constructor() : LockFreeLinkedListNode(), CompletionHandler {
    actual abstract override fun invoke(cause: Throwable?)
}

internal actual inline val CompletionHandlerBase.asHandler: CompletionHandler get() = this

internal actual abstract class CancelHandlerBase actual constructor() : CompletionHandler {
    actual abstract override fun invoke(cause: Throwable?)
}

internal actual inline val CancelHandlerBase.asHandler: CompletionHandler get() = this

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun CompletionHandler.invokeIt(cause: Throwable?) = invoke(cause)