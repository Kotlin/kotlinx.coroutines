// Platform-specific configuration to compile JVM modules

import org.gradle.api.*
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.dsl.abi.ExperimentalAbiValidation
import org.gradle.api.tasks.bundling.Jar

plugins {
    kotlin("jvm")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

kotlin {
    if (abiCheckEnabled) {
        @OptIn(ExperimentalAbiValidation::class)
        abiValidation {
            enabled = true
        }
    }

    compilerOptions {
        jvmTarget = JvmTarget.JVM_1_8
        configureGlobalKotlinArgumentsAndOptIns()
    }
    jvmToolchain(jdkToolchainVersion)
}

dependencies {
    testImplementation(kotlin("test"))
    // Workaround to make addSuppressed work in tests
    testImplementation(kotlin("reflect"))
    testImplementation(kotlin("stdlib-jdk7"))
    testImplementation(kotlin("test-junit"))
    testImplementation("junit:junit:${version("junit")}")
}

tasks.withType<Test> {
    testLogging {
        showStandardStreams = true
        events("passed", "failed")
    }
    val stressTest = project.properties["stressTest"]
    if (stressTest != null) systemProperties["stressTest"] = stressTest
}

// TODO: delete this after starting to use Kotlin 2.3.20
tasks.check {
    dependsOn(tasks.matching { it.name == "checkLegacyAbi" })
}

tasks.named<Jar>("jar") {
    fillManifestImplementationAttributes(project)
}
