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

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package guide.reactive.basic.example08

import io.reactivex.subjects.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.rx2.*
import kotlin.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking<Unit> {
    val subject = BehaviorSubject.create<String>()
    subject.onNext("one")
    subject.onNext("two")
    // now launch a coroutine to print the most recent update
    launch(coroutineContext) { // use the context of the main thread for a coroutine
        subject.consumeEach { println(it) }
    }
    subject.onNext("three")
    subject.onNext("four")
    yield() // yield the main thread to the launched coroutine <--- HERE
    subject.onComplete() // now complete subject's sequence to cancel consumer, too    
}
