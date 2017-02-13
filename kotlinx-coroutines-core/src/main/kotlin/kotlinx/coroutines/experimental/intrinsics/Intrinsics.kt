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

package kotlinx.coroutines.experimental.intrinsics

import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED

/**
 * Starts coroutine without receiver and with result type [T].
 * This function creates and start a new, fresh instance of suspendable computation every time it is invoked.
 * If the coroutine never suspends, then its result is returned directly,
 * otherwise it returns [COROUTINE_SUSPENDED] and the [completion] continuation is invoked when coroutine completes.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN", "UNCHECKED_CAST")
public fun <T> (suspend  () -> T).startCoroutineOrReturn(completion: Continuation<T>): Any? =
    (this as kotlin.jvm.functions.Function1<Continuation<T>, Any?>).invoke(completion)
