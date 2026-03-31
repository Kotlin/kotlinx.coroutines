package kotlinx.coroutines.validator

import org.junit.Test
import java.util.jar.*
import kotlin.test.*

class MavenPublicationMetaInfValidator {

    @Test
    fun testMetaInfCoreStructure() {
        val clazz = Class.forName("kotlinx.coroutines.Job")
        JarFile(clazz.protectionDomain.codeSource.location.file).checkMetaInfStructure(
            setOf(
                "MANIFEST.MF",
                "kotlinx-coroutines-core.kotlin_module",
                "com.android.tools/proguard/coroutines.pro",
                "com.android.tools/r8/coroutines.pro",
                "proguard/coroutines.pro",
                "versions/9/module-info.class",
                "kotlinx_coroutines_core.version"
            )
        )
    }

    @Test
    fun testMetaInfAndroidStructure() {
        val clazz = Class.forName("kotlinx.coroutines.android.HandlerDispatcher")
        val expectedEntries = buildSet {
            add("MANIFEST.MF")
            if (kotlinVersion.startsWith("2.4")) {
                add("org.jetbrains.kotlinx_kotlinx-coroutines-android.kotlin_module")
            } else {
                add("kotlinx-coroutines-android.kotlin_module")
            }
            add("services/kotlinx.coroutines.CoroutineExceptionHandler")
            add("services/kotlinx.coroutines.internal.MainDispatcherFactory")
            add("com.android.tools/r8-from-1.6.0/coroutines.pro")
            add("com.android.tools/r8-upto-3.0.0/coroutines.pro")
            add("com.android.tools/proguard/coroutines.pro")
            add("proguard/coroutines.pro")
            add("versions/9/module-info.class")
            add("kotlinx_coroutines_android.version")
        }
        JarFile(clazz.protectionDomain.codeSource.location.file)
            .checkMetaInfStructure(expectedEntries)
    }

    private fun JarFile.checkMetaInfStructure(expected: Set<String>) {
        val actual = HashSet<String>()
        for (e in entries()) {
            if (e.isDirectory() || !e.name.contains("META-INF")) {
                continue
            }
            val partialName = e.name.substringAfter("META-INF/")
            actual.add(partialName)
        }

        if (actual != expected) {
            val intersection = actual.intersect(expected)
            val mismatch = actual.subtract(intersection) + expected.subtract(intersection)
            fail("Mismatched files: " + mismatch)
        }

        close()
    }

    private val kotlinVersion: String
        get() = System.getProperty("kotlin.version.integration")
}
