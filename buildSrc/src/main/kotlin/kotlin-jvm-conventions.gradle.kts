// Platform-specific configuration to compile JVM modules

import org.gradle.api.*
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.dsl.abi.ExperimentalAbiValidation

plugins {
    kotlin("jvm")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

kotlin {
    @OptIn(ExperimentalAbiValidation::class)
    abiValidation {
        enabled = abiCheckEnabled
    }

    compilerOptions {
        jvmTarget = JvmTarget.JVM_1_8
        configureGlobalKotlinArgumentsAndOptIns()
    }
    jvmToolchain(jdkToolchainVersion)
}

dependencies {
    testImplementation(kotlin("test"))
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

tasks.check {
   dependsOn(tasks.checkLegacyAbi)
}
