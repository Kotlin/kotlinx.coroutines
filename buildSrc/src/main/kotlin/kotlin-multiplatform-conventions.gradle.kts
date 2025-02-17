import org.gradle.api.tasks.testing.logging.*
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.dsl.abi.ExperimentalAbiValidation

plugins {
    kotlin("multiplatform")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

kotlin {
    @OptIn(ExperimentalAbiValidation::class)
    abiValidation {
        enabled = abiCheckEnabled

        klib {
            enabled = true
        }
    }

    jvm {
        compilations.all {
            compileTaskProvider.configure {
                compilerOptions.jvmTarget = JvmTarget.JVM_1_8
            }
        }
    }
    jvmToolchain(jdkToolchainVersion)
    if (nativeTargetsAreEnabled) {
        // According to https://kotlinlang.org/docs/native-target-support.html
        // Tier 1
        linuxX64()
        macosX64()
        macosArm64()
        iosSimulatorArm64()
        iosX64()
        // Tier 2
        linuxArm64()
        watchosSimulatorArm64()
        watchosX64()
        watchosArm32()
        watchosArm64()
        tvosSimulatorArm64()
        tvosX64()
        tvosArm64()
        iosArm64()
        // Tier 3
        androidNativeArm32()
        androidNativeArm64()
        androidNativeX86()
        androidNativeX64()
        mingwX64()
        watchosDeviceArm64()
    }
    js {
        @Suppress("DEPRECATION", "DEPRECATION_ERROR") // KT-68597, KT-68597
        outputModuleName = project.name
        nodejs()
        compilations["main"]?.dependencies {
            api("org.jetbrains.kotlinx:atomicfu:${version("atomicfu")}")
        }
    }
    @OptIn(org.jetbrains.kotlin.gradle.ExperimentalWasmDsl::class)
    wasmJs {
        // Module name should be different from the one from JS
        // otherwise IC tasks that start clashing different modules with the same module name
        @Suppress("DEPRECATION", "DEPRECATION_ERROR") // KT-68597, KT-68597
        outputModuleName = project.name + "Wasm"
        nodejs()
        compilations["main"]?.dependencies {
            api("org.jetbrains.kotlinx:atomicfu:${version("atomicfu")}")
        }
    }
    @OptIn(org.jetbrains.kotlin.gradle.ExperimentalWasmDsl::class)
    wasmWasi {
        nodejs()
        compilations["main"]?.dependencies {
            api("org.jetbrains.kotlinx:atomicfu:${version("atomicfu")}")
        }
        compilations.configureEach {
            compileTaskProvider.configure {
                compilerOptions {
                    optIn.add("kotlin.wasm.internal.InternalWasmApi")
                }
            }
        }
    }
    applyDefaultHierarchyTemplate()
    sourceSets {
        commonTest {
            dependencies {
                api("org.jetbrains.kotlin:kotlin-test:${version("kotlin")}")
            }
        }
        jvmMain.dependencies {
            compileOnly("org.codehaus.mojo:animal-sniffer-annotations:1.20")
            // Workaround until https://github.com/JetBrains/kotlin/pull/4999 is picked up
            api("org.jetbrains:annotations:23.0.0")
        }
        jvmTest.dependencies {
            // Workaround to make addSuppressed work in tests
            api("org.jetbrains.kotlin:kotlin-reflect:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-stdlib-jdk7:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-test-junit:${version("kotlin")}")
            api("junit:junit:${version("junit")}")
        }
        nativeMain.dependencies {
            // workaround for #3968 until this is fixed on atomicfu's side
            api("org.jetbrains.kotlinx:atomicfu:0.23.1")
        }
        jsMain { }
        val wasmJsMain by getting {
        }
        val wasmJsTest by getting {
        }
        val wasmWasiMain by getting {
        }
        val wasmWasiTest by getting {
        }
        groupSourceSets("jsAndWasmShared", listOf("web", "wasmWasi"), listOf("common"))
    }

    @OptIn(org.jetbrains.kotlin.gradle.ExperimentalKotlinGradlePluginApi::class)
    compilerOptions {
        configureGlobalKotlinArgumentsAndOptIns()
        freeCompilerArgs.add("-Xexpect-actual-classes")
        optIn.add("kotlin.ExperimentalMultiplatform")
    }
}

// Disable intermediate sourceSet compilation because we do not need js-wasm common artifact
tasks.configureEach {
    if (name == "compileJsAndWasmSharedMainKotlinMetadata") {
        enabled = false
    }
    if (name == "compileJsAndWasmJsSharedMainKotlinMetadata") {
        enabled = false
    }
}

tasks.named("jvmTest", Test::class) {
    testLogging {
        showStandardStreams = true
        events = setOf(TestLogEvent.PASSED, TestLogEvent.FAILED)
    }
    project.properties["stressTest"]?.let { systemProperty("stressTest", it) }
}

tasks.check {
   dependsOn(tasks.checkLegacyAbi)
}
