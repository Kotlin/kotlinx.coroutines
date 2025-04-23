@file:JvmName("CommunityProjectsBuild")

import org.gradle.api.*
import org.gradle.api.artifacts.dsl.*
import org.gradle.api.tasks.testing.Test
import org.gradle.kotlin.dsl.*
import org.jetbrains.kotlin.gradle.dsl.KotlinCommonCompilerOptions
import java.net.*
import java.util.logging.*
import org.jetbrains.kotlin.gradle.dsl.KotlinVersion

private val LOGGER: Logger = Logger.getLogger("Kotlin settings logger")

/**
 * Functions in this file are responsible for configuring kotlinx.coroutines build against a custom dev version
 * of Kotlin compiler.
 * Such configuration is used in a composite community build of Kotlin in order to check whether not-yet-released changes
 * are compatible with our libraries (aka "integration testing that substitutes lack of unit testing").
 *
 * When `build_snapshot_train` is set to true (and [isSnapshotTrainEnabled] returns `true`),
 * - `kotlin_version property` is overridden with `kotlin_snapshot_version` (see [getOverriddenKotlinVersion]),
 * - `atomicfu_version` is overwritten by TeamCity environment (AFU is built with snapshot and published to mavenLocal
 *   as previous step or the snapshot build).
 * Additionally, mavenLocal and Sonatype snapshots are added to repository list and stress tests are disabled
 * (see [configureCommunityBuildTweaks]).
 *
 * DO NOT change the name of these properties without adapting the kotlinx.train build chain.
*/

/**
 * Should be used for running against of non-released Kotlin compiler on a system test level.
 *
 * @return a Kotlin API version parametrized from command line nor gradle.properties, null otherwise
 */
fun getOverriddenKotlinApiVersion(project: Project): KotlinVersion? {
    val apiVersion = project.rootProject.properties["kotlin_api_version"] as? String
    return if (apiVersion != null) {
        LOGGER.info("""Configured Kotlin API version: '$apiVersion' for project $${project.name}""")
        KotlinVersion.fromVersion(apiVersion)
    } else {
        null
    }
}

/**
 * Should be used for running against of non-released Kotlin compiler on a system test level
 *
 * @return a Kotlin Language version parametrized from command line nor gradle.properties, null otherwise
 */
fun getOverriddenKotlinLanguageVersion(project: Project): KotlinVersion? {
    val languageVersion = project.rootProject.properties["kotlin_language_version"] as? String
    return if (languageVersion != null) {
        LOGGER.info("""Configured Kotlin Language version: '$languageVersion' for project ${project.name}""")
        KotlinVersion.fromVersion(languageVersion)
    } else {
        null
    }
}

/**
 * Should be used for running against of non-released Kotlin compiler on a system test level
 * Kotlin compiler artifacts are expected to be downloaded from maven central by default.
 * In case of compiling with not-published into the MC kotlin compiler artifacts, a kotlin_repo_url gradle parameter should be specified.
 * To reproduce a build locally, a kotlin/dev repo should be passed
 *
 * @return an url for a kotlin compiler repository parametrized from command line nor gradle.properties, empty string otherwise
 */
fun getKotlinDevRepositoryUrl(project: Project): URI? {
    val url: String? = project.rootProject.properties["kotlin_repo_url"] as? String
    if (url != null) {
        LOGGER.info("""Configured Kotlin Compiler repository url: '$url' for project ${project.name}""")
        return URI.create(url)
    }
    return null
}

/**
 * Adds a kotlin-dev space repository with dev versions of Kotlin if Kotlin aggregate build is enabled
 */
fun addDevRepositoryIfEnabled(rh: RepositoryHandler, project: Project) {
    val devRepoUrl = getKotlinDevRepositoryUrl(project) ?: return
    rh.maven {
        url = devRepoUrl
    }
}

/**
 * Changes the build config when 'build_snapshot_train' is enabled:
 * Disables flaky and Kotlin-specific tests, prints the real version of Kotlin applied (to be sure overridden version of Kotlin is properly picked).
 */
fun Project.configureCommunityBuildTweaks() {
    if (!isSnapshotTrainEnabled(this)) return
    allprojects {
        // Disable stress tests and tests that are flaky on Kotlin version specific
        tasks.withType<Test>().configureEach {
            exclude("**/*LinearizabilityTest*")
            exclude("**/*LFTest*")
            exclude("**/*StressTest*")
            exclude("**/*scheduling*")
            exclude("**/*Timeout*")
            exclude("**/*definitely/not/kotlinx*")
            exclude("**/*PrecompiledDebugProbesTest*")
        }
    }

    LOGGER.info("Manifest of kotlin-compiler-embeddable.jar for coroutines")
    val coreProject = subprojects.single { it.name == coreModule }
    configure(listOf(coreProject)) {
        configurations.matching { it.name == "kotlinCompilerClasspath" }.configureEach {
            val config = resolvedConfiguration.files.single { it.name.contains("kotlin-compiler-embeddable") }

            val manifest = zipTree(config).matching {
                include("META-INF/MANIFEST.MF")
            }.files.single()

            manifest.readLines().forEach {
                println(it)
            }
        }
    }
}

/**
 * Ensures that, if [isSnapshotTrainEnabled] is true, the project is built with a snapshot version of Kotlin compiler.
 */
fun getOverriddenKotlinVersion(project: Project): String? =
    if (isSnapshotTrainEnabled(project)) {
        val snapshotVersion = project.rootProject.properties["kotlin_snapshot_version"]
            ?: error("'kotlin_snapshot_version' should be defined when building with a snapshot compiler")
        snapshotVersion.toString()
    } else {
        null
    }

/**
 * Checks if the project is built with a snapshot version of Kotlin compiler.
 */
fun isSnapshotTrainEnabled(project: Project): Boolean {
    val buildSnapshotTrain = project.rootProject.properties["build_snapshot_train"] as? String
    return !buildSnapshotTrain.isNullOrBlank()
}

fun shouldUseLocalMaven(project: Project): Boolean {
    val hasSnapshotDependency = project.rootProject.properties.any { (key, value) ->
        key.endsWith("_version") && value is String && value.endsWith("-SNAPSHOT").also {
            if (it) println("NOTE: USING SNAPSHOT VERSION: $key=$value")
        }
    }
    return hasSnapshotDependency || isSnapshotTrainEnabled(project)
}

/**
 * Returns a non-null value if the CI needs to override the default behavior of treating warnings as errors.
 * Then, `true` means that warnings should be treated as errors, `false` means that they should not.
 */
private fun warningsAreErrorsOverride(project: Project): Boolean? =
    when (val prop = project.rootProject.properties["kotlin_Werror_override"] as? String) {
        null -> null
        "enable" -> true
        "disable" -> false
        else -> error("Unknown value for 'kotlin_Werror_override': $prop")
    }

/**
 * Set warnings as errors, but allow the Kotlin User Project configuration to take over. See KT-75078.
 */
fun KotlinCommonCompilerOptions.setWarningsAsErrors(project: Project) {
    if (warningsAreErrorsOverride(project) != false) {
        allWarningsAsErrors = true
    } else {
        freeCompilerArgs.addAll("-Wextra", "-Xuse-fir-experimental-checkers")
    }
}

/**
 * Compiler flags required of Kotlin User Projects. See KT-75078.
 */
fun KotlinCommonCompilerOptions.configureKotlinUserProject() {
    freeCompilerArgs.addAll(
        "-Xreport-all-warnings", // emit warnings even if there are also errors
        "-Xrender-internal-diagnostic-names", // render the diagnostic names in CLI
    )
}

/**
 * Additional compiler flags passed on a case-by-case basis. Should be applied after the other flags.
 * See <https://github.com/Kotlin/kotlinx.coroutines/pull/4392#issuecomment-2775630200>
 */
fun KotlinCommonCompilerOptions.addExtraCompilerFlags(project: Project) {
    val extraOptions = project.rootProject.properties["kotlin_additional_cli_options"] as? String
    if (extraOptions != null) {
        LOGGER.info("""Adding extra compiler flags '$extraOptions' for a compilation in the project $${project.name}""")
        extraOptions.split(" ")?.forEach {
            if (it.isNotEmpty()) freeCompilerArgs.add(it)
        }
    }
}
