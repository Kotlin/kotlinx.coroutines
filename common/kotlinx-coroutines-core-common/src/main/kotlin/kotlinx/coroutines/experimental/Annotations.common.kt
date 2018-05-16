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

// NOTE: We are defining them in a special internalAnnotations package because they would break
// user code that uses kotlinx.coroutines library otherwise, see https://youtrack.jetbrains.com/issue/KT-23727
package kotlinx.coroutines.experimental.internalAnnotations

@Target(AnnotationTarget.FILE)
internal expect annotation class JvmName(val name: String)

@Target(AnnotationTarget.FILE)
internal expect annotation class JvmMultifileClass()

internal expect annotation class JvmField()

internal expect annotation class Volatile()

internal expect annotation class JsName(val name: String)
