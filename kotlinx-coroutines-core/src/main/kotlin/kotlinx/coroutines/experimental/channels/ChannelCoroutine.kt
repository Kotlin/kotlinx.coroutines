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

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.AbstractCoroutine
import kotlinx.coroutines.experimental.JobSupport
import kotlinx.coroutines.experimental.handleCoroutineException
import kotlin.coroutines.experimental.CoroutineContext

internal open class ChannelCoroutine<E>(
    override val parentContext: CoroutineContext,
    val channel: Channel<E>
) : AbstractCoroutine<Unit>(active = true), Channel<E> by channel {
    override fun afterCompletion(state: Any?, mode: Int) {
        val cause = (state as? JobSupport.CompletedExceptionally)?.cause
        if (!channel.close(cause) && cause != null)
            handleCoroutineException(context, cause)
    }
}
