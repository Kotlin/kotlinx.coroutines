/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.config.KotlinCompilerVersion
import org.jetbrains.kotlin.gradle.dsl.*
import org.gradle.kotlin.dsl.*

buildscript {
    if (shouldUseLocalMaven(rootProject)) {
        repositories {
            mavenLocal()
        }
    }

    repositories {
        mavenCentral()
        maven { url = java.net.URI("https://plugins.gradle.org/m2/") }
        addDevRepositoryIfEnabled(this, project)
        mavenLocal()
    }

    dependencies {
        // Please ensure that atomicfu-gradle-plugin is added to the classpath first, do not change the order, for details see #3984.
        // The corresponding issue in kotlinx-atomicfu: https://github.com/Kotlin/kotlinx-atomicfu/issues/384
        classpath("org.jetbrains.kotlinx:atomicfu-gradle-plugin:${version("atomicfu")}")
        classpath("org.jetbrains.kotlin:kotlin-gradle-plugin:${version("kotlin")}")
        classpath("org.jetbrains.dokka:dokka-gradle-plugin:${version("dokka")}")
        classpath("org.jetbrains.kotlinx:kotlinx-knit:${version("knit")}")
        classpath("org.jetbrains.kotlinx:binary-compatibility-validator:${version("binary_compatibility_validator")}")
        classpath("ru.vyarus:gradle-animalsniffer-plugin:${version("animalsniffer")}") // Android API check
        classpath("org.jetbrains.kotlin:atomicfu:${version("kotlin")}")
        classpath("org.jetbrains.kotlinx:kover-gradle-plugin:${version("kover")}")

        // JMH plugins
        classpath("gradle.plugin.com.github.johnrengelman:shadow:${version("shadow")}")
    }

    with(CacheRedirector) { buildscript.configureBuildScript(rootProject) }
}

// Configure subprojects with Kotlin sources
apply(plugin = "configure-compilation-conventions")

allprojects {
    val deployVersion = properties["DeployVersion"]
    if (deployVersion != null) version = deployVersion

    if (isSnapshotTrainEnabled(rootProject)) {
        val skipSnapshotChecks = rootProject.properties["skip_snapshot_checks"] != null
        if (!skipSnapshotChecks && version != version("atomicfu")) {
            throw IllegalStateException("Current deploy version is $version, but atomicfu version is not overridden (${version("atomicfu")}) for $this")
        }
    }

    if (shouldUseLocalMaven(rootProject)) {
        repositories {
            mavenLocal()
        }
    }

    // This project property is set during nightly stress test
    val stressTest = project.properties["stressTest"]
    // Copy it to all test tasks
    tasks.withType(Test::class).configureEach {
        if (stressTest != null) {
            systemProperty("stressTest", stressTest)
        }
    }
}

plugins {
    id("org.jetbrains.kotlinx.binary-compatibility-validator") version "0.13.2"
}

apply(plugin = "base")
apply(plugin = "kover-conventions")

apiValidation {
    ignoredProjects += unpublished + listOf("kotlinx-coroutines-bom")
    if (isSnapshotTrainEnabled(rootProject)) {
        ignoredProjects += coreModule
    }
    ignoredPackages += "kotlinx.coroutines.internal"
}

// Configure repositories
allprojects {
    repositories {
        /*
         * google should be first in the repository list because some of the play services
         * transitive dependencies was removed from jcenter, thus breaking gradle dependency resolution
         */
        google()
        mavenCentral()
        addDevRepositoryIfEnabled(this, project)
    }
}

// needs to be before evaluationDependsOn due to weird Gradle ordering
apply(plugin = "animalsniffer-conventions")

configure(subprojects.filter { !sourceless.contains(it.name) }) {
    if (isMultiplatform) {
        apply(plugin = "kotlin-multiplatform")
        apply(plugin = "kotlin-multiplatform-conventions")
    } else if (platformOf(this) == "jvm") {
        apply(plugin = "kotlin-jvm-conventions")
    } else {
        val platform = platformOf(this)
        throw IllegalStateException("No configuration rules for $platform")
    }
}

// Add dependency to the core module in all the other subprojects.
configure(subprojects.filter { !sourceless.contains(it.name) && it.name != coreModule }) {
    evaluationDependsOn(":$coreModule")
    val jvmTestDependency = project(":$coreModule")
        .extensions.getByType(KotlinMultiplatformExtension::class)
        .targets["jvm"].compilations["test"].output.allOutputs
    if (isMultiplatform) {
        configure<KotlinMultiplatformExtension> {
            sourceSets {
                commonMain {
                    dependencies {
                        api(project(":$coreModule"))
                    }
                }
                jvmTest {
                    dependencies {
                        implementation(jvmTestDependency)
                    }
                }
            }
        }
    } else {
        dependencies {
            add("api", project(":$coreModule"))
            // the only way IDEA can resolve test classes
            add("testImplementation", jvmTestDependency)
        }
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

// Report Kotlin compiler version when building project
println("Using Kotlin compiler version: ${KotlinCompilerVersion.VERSION}")

