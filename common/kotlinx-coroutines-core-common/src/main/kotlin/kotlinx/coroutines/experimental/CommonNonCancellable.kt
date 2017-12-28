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

public expect object NonCancellable : Job {
    override val isActive: Boolean
    override val isCompleted: Boolean
    override val isCancelled: Boolean
    override fun start(): Boolean
    suspend override fun join()
    override fun getCancellationException(): CancellationException
    override fun invokeOnCompletion(onCancelling: Boolean, invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle
    override fun cancel(cause: Throwable?): Boolean
    override val children: Sequence<Job>
    @Suppress("OverridingDeprecatedMember")
    override fun attachChild(child: Job): DisposableHandle
}
