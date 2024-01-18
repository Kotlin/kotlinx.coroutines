// This file was automatically generated from flow.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.exampleFlow01

fun simple(): List<Int> = listOf(1, 2, 3)
 
fun main() {
    simple().forEach { value -> println(value) } 
}
