/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import org.junit.Test
import java.io.*
import kotlin.test.*

/*
 * This is intentionally put here instead of coreAgentTest to avoid accidental classpath replacing
 * and ruining core agent test.
 */
class PrecompiledDebugProbesTest {

    private val overwrite = java.lang.Boolean.getBoolean("overwrite.probes")

    @Test
    fun testClassFileContent() {
        val clz = Class.forName("kotlin.coroutines.jvm.internal.DebugProbesKt")
        val className: String = clz.getName()
        val classFileResourcePath = className.replace(".", "/") + ".class"
        val stream = clz.classLoader.getResourceAsStream(classFileResourcePath)!!
        val array = stream.readBytes()
        // we expect the integration testing project to be in a subdirectory of the main kotlinx.coroutines project
        val base = File("").absoluteFile.parentFile
        val probes = File(base, "kotlinx-coroutines-core/jvm/resources/DebugProbesKt.bin")
        val binContent = probes.readBytes()
        if (overwrite) {
            FileOutputStream(probes).use { it.write(array) }
            println("Content was successfully overwritten!")
        } else {
            assertTrue(
                array.contentEquals(binContent),
                "Compiled DebugProbesKt.class does not match the file shipped as a resource in kotlinx-coroutines-core. " +
                        "Typically it happens because of the Kotlin version update (-> binary metadata). In that case, run the same test with -Poverwrite.probes=true."
            )
        }
    }
}
