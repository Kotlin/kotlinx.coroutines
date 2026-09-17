import org.gradle.api.tasks.testing.logging.TestLogEvent
import org.gradle.kotlin.dsl.invoke
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.dsl.abi.AbiValidationExtension
import org.jetbrains.kotlin.gradle.dsl.abi.ExperimentalAbiValidation
import org.jetbrains.kotlin.gradle.tasks.KotlinCompilationTask
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile

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

apply(plugin = "java-library")
apply(plugin = "org.jetbrains.kotlinx.atomicfu")

extensions.configure<JavaPluginExtension> {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

plugins.withId("org.jetbrains.kotlin.jvm") {
    extensions.configure<KotlinJvmProjectExtension> {
        if (abiCheckEnabled) {
            extensions.configure<AbiValidationExtension> {
                @OptIn(ExperimentalAbiValidation::class)
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
        if (hasSharedSources) {
            add("compileOnly", "org.codehaus.mojo:animal-sniffer-annotations:1.20")
            add("api", "org.jetbrains:annotations:23.0.0")
        }
        add("testImplementation", kotlin("test"))
        add("testImplementation", kotlin("test-junit"))
        add("testImplementation", "junit:junit:${version("junit")}")
    }

    tasks.named<Jar>("jar") {
        fillManifestImplementationAttributes(project)
    }
}

tasks.withType<Test> {
    testLogging {
        showStandardStreams = true
        events = setOf(TestLogEvent.PASSED, TestLogEvent.FAILED)
    }
    project.providers.gradleProperty("stressTest").orNull?.let { systemProperty("stressTest", it) }
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
        addExtraCompilerFlags(project)
    }
}
