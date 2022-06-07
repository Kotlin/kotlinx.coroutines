/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.validator

import org.junit.Test
import java.io.*
import java.net.*
import java.nio.file.*
import java.util.jar.*
import kotlin.io.path.*
import kotlin.test.*

class MavenPublicationVersionValidator {

    @Test
    fun testMppJar() {
        val clazz = Class.forName("kotlinx.coroutines.Job")
        clazz.checkUsingMavenLocal()
        JarFile(clazz.protectionDomain.codeSource.location.file).checkForVersion("kotlinx_coroutines_core.version")
    }

    @Test
    fun testAndroidJar() {
        val clazz = Class.forName("kotlinx.coroutines.android.HandlerDispatcher")
        clazz.checkUsingMavenLocal()
        JarFile(clazz.protectionDomain.codeSource.location.file).checkForVersion("kotlinx_coroutines_android.version")
    }

    private fun JarFile.checkForVersion(file: String) {
        val actualFile = "META-INF/$file"
        val version = System.getenv("version")
        use {
            for (e in entries()) {
                if (e.name == actualFile) {
                    val string = getInputStream(e).readAllBytes().decodeToString()
                    assertEquals(version, string)
                    return
                }
            }
            error("File $file not found")
        }
    }

    /**
     * Checks that [this] class was taken from the local Maven repository.
     */
    private fun Class<*>.checkUsingMavenLocal() {
        val file = File(protectionDomain.codeSource.location.file)
        val mavenLocal = URI(System.getenv("mavenLocalPath")).toPath()
        var directory = file.parentFile
        while (directory != null) {
            if (Files.isSameFile(mavenLocal, directory.toPath()))
                return
            directory = directory.parentFile
        }
        throw AssertionError("$file is not on the Maven local path $mavenLocal")
    }
}
