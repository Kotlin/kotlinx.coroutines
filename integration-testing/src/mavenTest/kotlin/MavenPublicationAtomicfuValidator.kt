/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.validator

import org.junit.*
import org.junit.Assert.assertTrue
import java.util.jar.*

class MavenPublicationAtomicfuValidator {
    private val ATOMIC_FU_REF = "Lkotlinx/atomicfu/".toByteArray()

    @Test
    fun testNoAtomicfuInClasspath() {
        val result = runCatching { Class.forName("kotlinx.atomicfu.AtomicInt") }
        assertTrue(result.exceptionOrNull() is ClassNotFoundException)
    }

    @Test
    fun testNoAtomicfuInMppJar() {
        val clazz = Class.forName("kotlinx.coroutines.Job")
        JarFile(clazz.protectionDomain.codeSource.location.file).checkForAtomicFu()
    }

    @Test
    fun testNoAtomicfuInAndroidJar() {
        val clazz = Class.forName("kotlinx.coroutines.android.HandlerDispatcher")
        JarFile(clazz.protectionDomain.codeSource.location.file).checkForAtomicFu()
    }

    private fun JarFile.checkForAtomicFu() {
        val foundClasses = mutableListOf<String>()
        for (e in entries()) {
            if (!e.name.endsWith(".class")) continue
            val bytes = getInputStream(e).use { it.readBytes() }
            loop@for (i in 0 until bytes.size - ATOMIC_FU_REF.size) {
                for (j in 0 until ATOMIC_FU_REF.size) {
                    if (bytes[i + j] != ATOMIC_FU_REF[j]) continue@loop
                }
                foundClasses += e.name // report error at the end with all class names
                break@loop
            }
        }
        if (foundClasses.isNotEmpty()) {
            error("Found references to atomicfu in jar file $name in the following class files: ${
            foundClasses.joinToString("") { "\n\t\t" + it }
            }")
        }
        close()
    }
}
