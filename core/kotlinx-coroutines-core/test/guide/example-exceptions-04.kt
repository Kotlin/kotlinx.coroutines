/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.exceptions04

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

fun main(args: Array<String>) = runBlocking {
     val handler = CoroutineExceptionHandler { _, exception -> println("Caught $exception") }
   
       val job = launch(handler) {
           val child1 = launch(coroutineContext, start = CoroutineStart.ATOMIC) {
               try {
                   delay(Long.MAX_VALUE)
               } finally {
                   withContext(NonCancellable) {
                       println("Children are cancelled, but exception is not handled until children are terminated completely")
                       delay(100)
                       println("Last child finished its non cancellable block")
                   }
               }
           }
   
           val child2 = launch(coroutineContext, start = CoroutineStart.ATOMIC) {
               delay(10)
               println("Child throws an exception")
               throw ArithmeticException()
           }
       }
   
       job.join()
}
