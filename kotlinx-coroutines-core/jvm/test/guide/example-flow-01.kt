/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from flow.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleFlow01

fun foo(): List<Int> = listOf(1, 2, 3)
 
fun main() {
    foo().forEach { value -> println(value) } 
}
