import org.gradle.api.tasks.testing.logging.TestLogEvent
import org.gradle.kotlin.dsl.invoke
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.tasks.Kotlin2JsCompile
import org.jetbrains.kotlin.gradle.tasks.KotlinCompilationTask
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile
import org.jetbrains.kotlin.gradle.tasks.KotlinNativeCompile
import org.jetbrains.kotlin.gradle.targets.jvm.KotlinJvmTarget

private fun KotlinCommonCompilerOptions.configureGlobalKotlinArgumentsAndOptIns() {
    freeCompilerArgs.addAll("-progressive")
    optIn.addAll(
        "kotlin.experimental.ExperimentalTypeInference",
        "kotlin.js.ExperimentalJsExport",
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

// Workaround to support both KGP 2.3 and 2.5+
private fun ExtensionAware.enableAbiValidation() {
    val oldAbiValidation = extensions.findByName("abiValidation")
    if (oldAbiValidation != null) {
        oldAbiValidation.withGroovyBuilder {
            setProperty("enabled", true)
        }
    } else {
        withGroovyBuilder {
            // enable by invoke `abiValidation()` function
            "abiValidation"()
        }
    }
}

plugins.withId("org.jetbrains.kotlin.jvm") {
    extensions.configure<KotlinJvmProjectExtension> {
        if (abiCheckEnabled) {
            enableAbiValidation()
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

    tasks.named<Jar>("jar") {
        fillManifestImplementationAttributes(project)
    }
}

plugins.withId("org.jetbrains.kotlin.multiplatform") {
    extensions.configure<KotlinMultiplatformExtension> {
        if (abiCheckEnabled) {
            enableAbiValidation()
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
        macosArm64()
        iosSimulatorArm64()
        // Tier 2
        linuxArm64()
        watchosSimulatorArm64()
        watchosArm64()
        tvosSimulatorArm64()
        tvosArm64()
        iosArm64()
        // Tier 3
        iosX64()
        mingwX64()
        watchosDeviceArm64()

        // Deprecated for removal: see KT-86581
        @Suppress("DEPRECATION", "DEPRECATION_ERROR")
        run {
            androidNativeArm32()
            androidNativeArm64()
            androidNativeX86()
            androidNativeX64()
        }
        // Deprecated for removal: see KT-78660
        @Suppress("DEPRECATION", "DEPRECATION_ERROR")
        run {
            macosX64()
            tvosX64()
            watchosX64()
        }
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

        targets.withType<KotlinJvmTarget>().configureEach {
            // Fill attributes for the JVM implementation Jar only
            tasks.named<Jar>(artifactsTaskName) {
                fillManifestImplementationAttributes(project)
            }
        }
    }

    // Disable intermediate sourceSet compilation because we do not need js-wasm common artifact
    tasks.configureEach {
        if (name == "compileJsAndWasmSharedMainKotlinMetadata") {
            enabled = false
        }
    }

    /*
     * To avoid a conflict with a JPMS module provided by kotlinx-coroutines-*-jvm artifacts,
     * an explicit automatic module name has to be specified in the manifest for metadata jars.
     */
    tasks.named("allMetadataJar", Jar::class) {
        val moduleName =  project.name.replace("-", ".") + ".artifact_disambiguating_module"
        manifest {
            attributes("Automatic-Module-Name" to moduleName)
        }
    }
}

tasks.withType<Test> {
    testLogging {
        showStandardStreams = true
        events = setOf(TestLogEvent.PASSED, TestLogEvent.FAILED)
    }
    project.providers.gradleProperty("stressTest").orNull?.let { systemProperty("stressTest", it) }
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
        if (this@configureEach is Kotlin2JsCompile) {
            freeCompilerArgs.add("-Xklib-ir-inliner=intra-module")
        }
        if (this@configureEach is KotlinNativeCompile) {
            optIn.addAll(
                "kotlinx.cinterop.ExperimentalForeignApi",
                "kotlinx.cinterop.UnsafeNumber",
                "kotlin.experimental.ExperimentalNativeApi",
                "kotlin.native.concurrent.ObsoleteWorkersApi",
            )
            freeCompilerArgs.add("-Xklib-ir-inliner=intra-module")
        }
        addExtraCompilerFlags(project)
    }
}
