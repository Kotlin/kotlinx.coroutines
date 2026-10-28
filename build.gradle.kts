import org.jetbrains.kotlin.gradle.dsl.*
import org.gradle.kotlin.dsl.*

buildscript {
    with(CacheRedirector) { buildscript.configureBuildScript(rootProject) }
}

allprojects {
    val deployVersion = providers.gradleProperty("DeployVersion").orNull
    if (deployVersion != null) version = deployVersion

    if (isSnapshotTrainEnabled(rootProject)) {
        val skipSnapshotChecks = providers.gradleProperty("skip_snapshot_checks").isPresent
        if (!skipSnapshotChecks && version != version("atomicfu")) {
            throw IllegalStateException("Current deploy version is $version, but atomicfu version is not overridden (${version("atomicfu")}) for $this")
        }
    }

    // This project property is set during nightly stress test
    val stressTest = project.providers.gradleProperty("stressTest").orNull
    // Copy it to all test tasks
    tasks.withType(Test::class).configureEach {
        if (stressTest != null) {
            systemProperty("stressTest", stressTest)
        }
    }
}

apply(plugin = "base")
apply(plugin = "kover-conventions")

configure(subprojects.filter { !sourceless.contains(it.name) }) {
    if (isMultiplatform) {
        apply(plugin = "kotlin-multiplatform")
    } else {
        apply(plugin = "kotlin")
    }
    apply(plugin = "kotlin-shared-conventions")
}

// needs to be before evaluationDependsOn due to weird Gradle ordering
configure(subprojects) {
    fun Project.shouldSniff(): Boolean =
        project.name !in unpublished && project.name !in sourceless
            && project.name !in androidNonCompatibleProjects
    // Skip JDK 8 projects or unpublished ones
    if (shouldSniff()) {
        apply(plugin = "animalsniffer-shared-conventions")
    }
}

configure(subprojects.filter { !sourceless.contains(it.name) && it.name != testUtilsModule }) {
    if (isMultiplatform) {
        configure<KotlinMultiplatformExtension> {
            sourceSets.commonTest.dependencies { implementation(project(":$testUtilsModule")) }
        }
    } else {
        dependencies { add("testImplementation", project(":$testUtilsModule")) }
    }
}

// Add dependency to the core module in all the other subprojects.
configure(subprojects.filter { !sourceless.contains(it.name) && it.name != coreModule }) {
    evaluationDependsOn(":$coreModule")
    if (isMultiplatform) {
        configure<KotlinMultiplatformExtension> {
            sourceSets.commonMain.dependencies { api(project(":$coreModule")) }
        }
    } else {
        dependencies { add("api", project(":$coreModule")) }
    }
}

apply(plugin = "bom-conventions")
apply(plugin = "java-modularity-conventions")
apply(plugin = "version-file-conventions")

rootProject.configureCommunityBuildTweaks()

apply(plugin = "source-set-conventions")
apply(plugin = "dokka-conventions")
apply(plugin = "knit-conventions")

/*
 * TODO: core and non-core cannot be configured via 'configure(subprojects)'
 * because of 'afterEvaluate' issue. This one should be migrated to
 * `plugins { id("pub-conventions") }` eventually
 */
configure(subprojects.filter {
    !unpublished.contains(it.name) && it.name != coreModule
}) {
    apply(plugin = "pub-conventions")
}

AuxBuildConfiguration.configure(rootProject)
rootProject.registerTopLevelDeployTask()
