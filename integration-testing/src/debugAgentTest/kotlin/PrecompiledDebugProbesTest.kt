/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import org.junit.Test
import kotlin.test.*

/*
 * This is intentionally put here instead of coreAgentTest to avoid accidental classpath replacing
 * and ruining core agent test.
 */
class PrecompiledDebugProbesTest {

    @Test
    fun testClassFileContent() {
        val clz = Class.forName("kotlin.coroutines.jvm.internal.DebugProbesKt")
        val className: String = clz.getName()
        val classFileResourcePath = className.replace(".", "/") + ".class"
        val stream = clz.classLoader.getResourceAsStream(classFileResourcePath)!!
        val array = stream.readBytes()
        val binFile = clz.classLoader.getResourceAsStream("DebugProbesKt.bin")!!
        val binContent = binFile.readBytes()
        assertTrue(array.contentEquals(binContent))
    }

    private fun diffpos(a: ByteArray, b: ByteArray, typeLenght: Int): Int {
        if (a.size == b.size) {
            for (i in a.indices) {
                if (a[i] != b[i]) {
                    println(i)
                }
            }
        }
        return -1
    }
}