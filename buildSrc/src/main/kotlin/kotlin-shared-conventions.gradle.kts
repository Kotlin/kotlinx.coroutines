import org.gradle.api.tasks.testing.logging.TestLogEvent
import org.gradle.kotlin.dsl.invoke
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.dsl.abi.AbiValidationExtension
import org.jetbrains.kotlin.gradle.dsl.abi.AbiValidationMultiplatformExtension
import org.jetbrains.kotlin.gradle.dsl.abi.ExperimentalAbiValidation
import org.jetbrains.kotlin.gradle.tasks.KotlinCompilationTask
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile
import org.jetbrains.kotlin.gradle.tasks.KotlinNativeCompile

private fun KotlinCommonCompilerOptions.configureGlobalKotlinArgumentsAndOptIns() {
    freeCompilerArgs.addAll("-progressive")
    optIn.addAll(
        "kotlin.experimental.ExperimentalTypeInference",
        // our own opt-ins that we don't want to bother with in our own code:
        "kotlinx.coroutines.DelicateCoroutinesApi",
        "kotlinx.coroutines.ExperimentalCoroutinesApi",
        "kotlinx.coroutines.ObsoleteCoroutinesApi",
        "kotlinx.coroutines.InternalCoroutinesApi",
        "kotlinx.coroutines.FlowPreview"
    )
}

apply(plugin = "org.jetbrains.kotlinx.atomicfu")

extensions.configure<JavaPluginExtension> {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

plugins.withId("org.jetbrains.kotlin.jvm") {
    extensions.configure<KotlinJvmProjectExtension> {
        extensions.configure<AbiValidationExtension> {
            @OptIn(ExperimentalAbiValidation::class)
            enabled = abiCheckEnabled
        }
        compilerOptions {
            jvmTarget = JvmTarget.JVM_1_8
            configureGlobalKotlinArgumentsAndOptIns()
        }
        jvmToolchain(jdkToolchainVersion)
    }

    dependencies {
        add("testImplementation", kotlin("test"))
        add("testImplementation", kotlin("test-junit"))
        add("testImplementation", "junit:junit:${version("junit")}")
    }
}

plugins.withId("org.jetbrains.kotlin.multiplatform") {
    extensions.configure<KotlinMultiplatformExtension> {
        extensions.configure<AbiValidationMultiplatformExtension> {
            @OptIn(ExperimentalAbiValidation::class)
            enabled = abiCheckEnabled
        }
        jvm {
            compilations.all {
                compileTaskProvider.configure {
                    compilerOptions.jvmTarget = JvmTarget.JVM_1_8
                }
            }
        }
        jvmToolchain(jdkToolchainVersion)
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
        js {
            outputModuleName = project.name
            nodejs()
        }
        @OptIn(org.jetbrains.kotlin.gradle.ExperimentalWasmDsl::class)
        wasmJs {
            // Module name should be different from the one from JS
            // otherwise IC tasks that start clashing different modules with the same module name
            outputModuleName = project.name + "Wasm"
            nodejs()
        }
        @OptIn(org.jetbrains.kotlin.gradle.ExperimentalWasmDsl::class)
        wasmWasi {
            nodejs()
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
            commonTest.dependencies {
                implementation("org.jetbrains.kotlin:kotlin-test:${version("kotlin")}")
            }
            jvmMain.dependencies {
                compileOnly("org.codehaus.mojo:animal-sniffer-annotations:1.20")
                // Workaround until https://github.com/JetBrains/kotlin/pull/4999 is picked up
                api("org.jetbrains:annotations:23.0.0")
            }
            jvmTest.dependencies {
                implementation("org.jetbrains.kotlin:kotlin-test-junit:${version("kotlin")}")
                implementation("junit:junit:${version("junit")}")
            }
            groupSourceSets("jsAndWasmShared", listOf("web", "wasmWasi"), listOf("common"))
        }

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
}

tasks.withType<Test> {
    testLogging {
        showStandardStreams = true
        events = setOf(TestLogEvent.PASSED, TestLogEvent.FAILED)
    }
    project.properties["stressTest"]?.let { systemProperty("stressTest", it) }
}

tasks.named("check") {
    dependsOn(tasks.named("checkLegacyAbi"))
}

tasks.withType<KotlinCompilationTask<*>>().configureEach {
    val isMainTaskName = name.startsWith("compileKotlin")
    compilerOptions {
        getOverriddenKotlinLanguageVersion(project)?.let {
            languageVersion = it
        }
        getOverriddenKotlinApiVersion(project)?.let {
            apiVersion = it
        }
        if (isMainTaskName && !unpublished.contains(project.name)) {
            setWarningsAsErrors(project)
            freeCompilerArgs.addAll(
                "-Xexplicit-api=strict",
                "-Xdont-warn-on-error-suppression",
            )
        }
        configureKotlinUserProject()
        /* Coroutines do not interop with Java and these flags provide a significant
         * (i.e. close to double-digit) reduction in both bytecode and optimized dex size */
        if (this@configureEach is KotlinJvmCompile) {
            freeCompilerArgs.addAll(
                "-Xno-param-assertions",
                "-Xno-call-assertions",
                "-Xno-receiver-assertions",
            )
        }
        if (this@configureEach is KotlinNativeCompile) {
            optIn.addAll(
                "kotlinx.cinterop.ExperimentalForeignApi",
                "kotlinx.cinterop.UnsafeNumber",
                "kotlin.experimental.ExperimentalNativeApi",
                "kotlin.native.concurrent.ObsoleteWorkersApi",
            )
        }
        addExtraCompilerFlags(project)
    }
}
