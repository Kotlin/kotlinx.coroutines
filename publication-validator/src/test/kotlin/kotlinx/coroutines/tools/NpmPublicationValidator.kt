/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.validator

import com.google.gson.*
import org.apache.commons.compress.archivers.tar.*
import org.junit.*
import java.io.*
import java.util.zip.*

class NpmPublicationValidator {
    private val VERSION = System.getenv("DeployVersion")
    private val BUILD_DIR = System.getenv("teamcity.build.checkoutDir")
    private val NPM_ARTIFACT = "$BUILD_DIR/kotlinx-coroutines-core/build/npm/kotlinx-coroutines-core-$VERSION.tgz"

    @Test
    fun testPackageJson() {
        println("Checking dependencies of $NPM_ARTIFACT")
        val visited = visit("package.json") {
            val json = JsonParser().parse(content()).asJsonObject
            assertEquals(VERSION, json["version"].asString)
            assertNull(json["dependencies"])
            val peerDependencies = json["peerDependencies"].asJsonObject
            assertEquals(1, peerDependencies.size())
            assertNotNull(peerDependencies["kotlin"])
        }
        assertEquals(1, visited)
    }

    @Test
    fun testAtomicfuDependencies() {
        println("Checking contents of $NPM_ARTIFACT")
        val visited = visit(".js") {
            val content = content()
            assertFalse(content, content.contains("atomicfu", true))
            assertFalse(content, content.contains("atomicint", true))
            assertFalse(content, content.contains("atomicboolean", true))
        }
        assertEquals(2, visited)
    }

    private fun InputStream.content(): String {
        val bais = ByteArrayOutputStream()
        val buffer = ByteArray(DEFAULT_BUFFER_SIZE)
        var read = read(buffer, 0, DEFAULT_BUFFER_SIZE)
        while (read >= 0) {
            bais.write(buffer, 0, read)
            read = read(buffer, 0, DEFAULT_BUFFER_SIZE)
        }
        return bais.toString()
    }

    private inline fun visit(fileSuffix: String, block: InputStream.(entry: TarArchiveEntry) -> Unit): Int {
        var visited = 0
        TarArchiveInputStream(GZIPInputStream(FileInputStream(NPM_ARTIFACT))).use { tais ->
            var entry: TarArchiveEntry? = tais.nextTarEntry ?: return 0
            do {
                if (entry!!.name.endsWith(fileSuffix)) {
                    ++visited
                    tais.block(entry)
                }
                entry = tais.nextTarEntry
            } while (entry != null)

            return visited
        }
    }
}
