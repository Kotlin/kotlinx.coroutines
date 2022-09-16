/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.validator

import org.junit.Test
import org.objectweb.asm.*
import org.objectweb.asm.ClassReader.*
import org.objectweb.asm.ClassWriter.*
import org.objectweb.asm.Opcodes.*
import java.util.jar.*
import kotlin.test.*

class MavenPublicationAtomicfuValidator {
    private val ATOMIC_FU_REF = "Lkotlinx/atomicfu/".toByteArray()
    private val KOTLIN_METADATA_DESC = "Lkotlin/Metadata;"

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
            // check the bytecode of the class for ATOMIC_FU_REF excluding metadata
            val bytes = getInputStream(e).use { it.readBytes() }
            val outBytes = bytes.eraseMetadata()
            // The atomicfu compiler plugin does not remove atomic properties from metadata,
            // so for now we check that there are no ATOMIC_FU_REF left in the class bytecode excluding metadata.
            // This may be reverted after the fix in the compiler plugin transformer (for Kotlin 1.8.0).
            if (outBytes.checkBytes()) {
                foundClasses += e.name // report error at the end with all class names
            }
        }
        if (foundClasses.isNotEmpty()) {
            error("Found references to atomicfu in jar file $name in the following class files: ${
                foundClasses.joinToString("") { "\n\t\t" + it }
            }")
        }
        close()
    }

    private fun ByteArray.checkBytes(): Boolean {
        loop@for (i in 0 until this.size - ATOMIC_FU_REF.size) {
            for (j in 0 until ATOMIC_FU_REF.size) {
                if (this[i + j] != ATOMIC_FU_REF[j]) continue@loop
            }
            return true
        }
        return false
    }

    private fun ByteArray.eraseMetadata(): ByteArray {
        val cw = ClassWriter(COMPUTE_MAXS or COMPUTE_FRAMES)
        ClassReader(this).accept(object : ClassVisitor(ASM9, cw) {
            override fun visitAnnotation(descriptor: String?, visible: Boolean): AnnotationVisitor? {
                return if (descriptor == KOTLIN_METADATA_DESC) null else super.visitAnnotation(descriptor, visible)
            }
        }, SKIP_FRAMES)
        return cw.toByteArray()
    }
}
