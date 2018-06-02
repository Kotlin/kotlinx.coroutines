package kotlinx.coroutines.experimental.tools

import org.junit.*
import org.junit.rules.*
import java.io.*
import java.util.jar.*

class PublicApiTest {

   /*
    * How to add a test for your module kotlinx-coroutines-foo?
    *
    * Dump public declarations via PublicApiDump.kt and create file
    * reference-public-api/kotlinx-coroutines-foo.txt with dumped declarations.
    *
    * Then add test:
    *
    * @Test
    * fun kotlinxCorountesFoo() { // <- name pattern should match txt file from reference-public-api
    *   snapshotAPIAndCompare($relative_path_to_module)
    * }
    */

    @Rule
    @JvmField
    val testName = TestName()

    @Test
    fun kotlinxCoroutinesCore() {
        snapshotAPIAndCompare("core/kotlinx-coroutines-core", nonPublicPackages = listOf("kotlinx.coroutines.experimental.internal"))
    }

    @Test
    fun kotlinxCoroutinesReactive() {
        snapshotAPIAndCompare("reactive/kotlinx-coroutines-reactive")
    }

    @Test
    fun kotlinxCoroutinesReactor() {
        snapshotAPIAndCompare("reactive/kotlinx-coroutines-reactor")
    }

    @Test
    fun kotlinxCoroutinesRx1() {
        snapshotAPIAndCompare("reactive/kotlinx-coroutines-rx1")
    }

    @Test
    fun kotlinxCoroutinesRx2() {
        snapshotAPIAndCompare("reactive/kotlinx-coroutines-rx2")
    }

    @Test
    fun kotlinxCoroutinesGuava() {
        snapshotAPIAndCompare("integration/kotlinx-coroutines-guava")
    }

    @Test
    fun kotlinxCoroutinesJdk8() {
        snapshotAPIAndCompare("integration/kotlinx-coroutines-jdk8")
    }


    @Test
    fun kotlinxCoroutinesNio() {
        snapshotAPIAndCompare("integration/kotlinx-coroutines-nio")
    }

    @Test
    fun kotlinxCoroutinesQuasar() {
        snapshotAPIAndCompare("integration/kotlinx-coroutines-quasar")
    }

    @Test
    fun kotlinxCoroutinesAndroid() {
        snapshotAPIAndCompare("ui/kotlinx-coroutines-android")
    }


    @Test
    fun kotlinxCoroutinesJavafx() {
        snapshotAPIAndCompare("ui/kotlinx-coroutines-javafx")
    }

    @Test
    fun kotlinxCoroutinesSwing() {
        snapshotAPIAndCompare("ui/kotlinx-coroutines-swing")
    }

    private fun snapshotAPIAndCompare(basePath: String, jarPattern: String = basePath.substring(basePath.indexOf("/") + 1),
                                      publicPackages: List<String> = emptyList(), nonPublicPackages: List<String> = emptyList()) {
        val base = File("../$basePath/build/libs").absoluteFile.normalize()
        val jarFile = getJarPath(base, jarPattern)
        val kotlinJvmMappingsFiles = listOf(base.resolve("../visibilities.json"))

        println("Reading kotlin visibilities from $kotlinJvmMappingsFiles")
        val publicPackagePrefixes = publicPackages.map { it.replace('.', '/') + '/' }
        val visibilities =
                kotlinJvmMappingsFiles
                        .map { readKotlinVisibilities(it).filterKeys { name -> publicPackagePrefixes.none { name.startsWith(it) } } }
                        .reduce { m1, m2 -> m1 + m2 }

        println("Reading binary API from $jarFile")
        val api = getBinaryAPI(JarFile(jarFile), visibilities).filterOutNonPublic(nonPublicPackages)

        val target = File("reference-public-api")
                .resolve(testName.methodName.replaceCamelCaseWithDashedLowerCase() + ".txt")

        api.dumpAndCompareWith(target)
    }

    private fun getJarPath(base: File, jarPattern: String, kotlinVersion: String? = null): File {
        val versionPattern = kotlinVersion?.let { "-" + Regex.escape(it) } ?: ".+"
        val regex = Regex("$jarPattern$versionPattern\\.jar")
        val files = (base.listFiles() ?: throw Exception("Cannot list files in $base"))
            .filter { it.name.let {
                    it matches regex
                    && !it.endsWith("-sources.jar")
                    && !it.endsWith("-javadoc.jar")
                    && !it.endsWith("-tests.jar")} }

        return files.singleOrNull() ?: throw Exception("No single file matching $regex in $base:\n${files.joinToString("\n")}")
    }
}
