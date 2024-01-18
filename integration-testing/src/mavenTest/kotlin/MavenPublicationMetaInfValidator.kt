package kotlinx.coroutines.validator

import org.junit.Test
import org.objectweb.asm.*
import org.objectweb.asm.ClassReader.*
import org.objectweb.asm.ClassWriter.*
import org.objectweb.asm.Opcodes.*
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
        JarFile(clazz.protectionDomain.codeSource.location.file).checkMetaInfStructure(
            setOf(
                "MANIFEST.MF",
                "kotlinx-coroutines-android.kotlin_module",
                "services/kotlinx.coroutines.CoroutineExceptionHandler",
                "services/kotlinx.coroutines.internal.MainDispatcherFactory",
                "com.android.tools/r8-from-1.6.0/coroutines.pro",
                "com.android.tools/r8-upto-3.0.0/coroutines.pro",
                "com.android.tools/proguard/coroutines.pro",
                "proguard/coroutines.pro",
                "versions/9/module-info.class",
                "kotlinx_coroutines_android.version"
            )
        )
    }

    private fun JarFile.checkMetaInfStructure(expected: Set<String>) {
        val actual = HashSet<String>()
        for (e in entries()) {
            if (e.isDirectory() || !e.realName.contains("META-INF")) {
                continue
            }
            val partialName = e.realName.substringAfter("META-INF/")
            actual.add(partialName)
        }

        if (actual != expected) {
            val intersection = actual.intersect(expected)
            val mismatch = actual.subtract(intersection) + expected.subtract(intersection)
            fail("Mismatched files: " + mismatch)
        }

        close()
    }
}
