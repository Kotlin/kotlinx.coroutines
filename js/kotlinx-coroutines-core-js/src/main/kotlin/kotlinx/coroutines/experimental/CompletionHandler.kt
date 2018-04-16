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

internal actual abstract class CompletionHandlerNode : LinkedListNode() {
    @Suppress("UnsafeCastFromDynamic")
    actual inline val asHandler: CompletionHandler get() = asDynamic()
    actual abstract fun invoke(cause: Throwable?)
}

internal actual abstract class CancellationHandler {
    @Suppress("UnsafeCastFromDynamic")
    actual inline val asHandler: CompletionHandler get() = asDynamic()
    actual abstract fun invoke(cause: Throwable?)
}

internal actual fun CompletionHandler.invokeIt(cause: Throwable?) {
    when(jsTypeOf(this)) {
        "function" -> invoke(cause)
        else -> (this as CompletionHandlerNode).invoke(cause)
    }
}
