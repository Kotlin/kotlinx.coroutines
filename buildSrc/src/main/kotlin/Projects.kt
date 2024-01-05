@file:JvmName("Projects")

import org.gradle.api.*
import org.gradle.api.tasks.*

fun Project.version(target: String): String {
    if (target == "kotlin") {
        getOverriddenKotlinVersion(this)?.let { return it }
    }
    return property("${target}_version") as String
}

val Project.jdkToolchainVersion: Int get() = property("jdk_toolchain_version").toString().toInt()

/**
 * TODO: check if this is still relevant.
 * It was introduced in <https://github.com/Kotlin/kotlinx.coroutines/pull/2389>, and the project for which this was
 * done is already long finished.
 */
val Project.nativeTargetsAreEnabled: Boolean get() = rootProject.properties["disable_native_targets"] == null

val Project.sourceSets: SourceSetContainer
    get() = extensions.getByName("sourceSets") as SourceSetContainer

val coreModule = "kotlinx-coroutines-core"
val jdk8ObsoleteModule = "kotlinx-coroutines-jdk8"
val testUtilsModule = "test-utils"

// Not applicable for Kotlin plugin
val sourceless = setOf("kotlinx.coroutines", "kotlinx-coroutines-bom")

// Not published
val unpublished = setOf("kotlinx.coroutines", "benchmarks", "android-unit-tests", testUtilsModule)

val Project.isMultiplatform: Boolean get() = name in setOf(coreModule, "kotlinx-coroutines-test", testUtilsModule)
val Project.isBom: Boolean get() = name == "kotlinx-coroutines-bom"

// Projects that we do not check for Android API level 14 check due to various limitations
val androidNonCompatibleProjects = setOf(
    "kotlinx-coroutines-debug",
    "kotlinx-coroutines-swing",
    "kotlinx-coroutines-javafx",
    "kotlinx-coroutines-jdk8",
    "kotlinx-coroutines-jdk9",
    "kotlinx-coroutines-reactor",
    "kotlinx-coroutines-test"
)
