/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.tasks.testing.*
import org.gradle.kotlin.dsl.*
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.plugin.*
import org.jetbrains.kotlin.gradle.plugin.mpp.*
import org.jetbrains.kotlin.gradle.targets.native.tasks.*
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile
import org.jetbrains.kotlin.gradle.testing.*
import org.jetbrains.kotlin.konan.target.*
import java.io.*

plugins {
    kotlin("multiplatform")
    id("org.jetbrains.kotlinx.benchmark")
    id("org.jetbrains.dokka")
    id("org.jetbrains.kotlinx.kover")
}

apply(plugin = "pub-conventions")

/* ==========================================================================
  Configure source sets structure for kotlinx-coroutines-core:

     TARGETS                            SOURCE SETS
     -------         ----------------------------------------------
     wasmJs \----------> jsAndWasmShared --------------------+
     js     /                                                |
                                                             V
     jvmCore\ --------> jvm ---------> concurrent -------> common
     jdk8   /                           ^
                                        |
     ios     \                          |
     macos   | ---> nativeDarwin ---> native ---+
     tvos    |                         ^
     watchos /                         |
                                       |
     linux  \  ---> nativeOther -------+
     mingw  /


Explanation of JVM source sets structure:

The overall structure is just a hack to support the scenario we are interested in:

* We would like to have two source-sets "core" and "jdk8"
* "jdk8" is allowed to use API from Java 8 and from "core"
* "core" is prohibited to use any API from "jdk8"
* It is okay to have tests in a single test source-set
* And we want to publish a **single** artifact kotlinx-coroutines-core.jar that contains classes from both source-sets
* Current limitation: only classes from "core" are checked with animal-sniffer

For that, we have following compilations:
* jvmMain compilation: [jvmCoreMain, jdk8Main]
* jvmCore compilation:  [commonMain]
* jdk8    compilation: [commonMain, jvmCoreMain]

Theoretically, "jvmCore" could've been "jvmMain", it is not for technical reasons,
here is the explanation from Seb:

"""
The jvmCore is theoretically not necessary. All code for jdk6 compatibility can be in jvmMain and jdk8 dependent code can be in jdk8Main.
Effectively there is no reason for ever putting code into jvmCoreMain.
However, when creating a new compilation, we have to take care of creating a defaultSourceSet. Without creating the jvmCoreMain source set,
 the creation of the compilation fails. That is the only reason for this source set.
"""
 ========================================================================== */

val sourceSetSuffixes = listOf("Main", "Test")

fun defineSourceSet(newName: String, dependsOn: List<String>, includedInPred: (String) -> Boolean) {
    for (suffix in sourceSetSuffixes) {
        val newSS = kotlin.sourceSets.maybeCreate(newName + suffix)
        for (dep in dependsOn) {
            newSS.dependsOn(kotlin.sourceSets[dep + suffix])
        }
        for (curSS in kotlin.sourceSets) {
            val curName = curSS.name
            if (curName.endsWith(suffix)) {
                val prefix = curName.substring(0, curName.length - suffix.length)
                if (includedInPred(prefix)) curSS.dependsOn(newSS)
            }
        }
    }
}

fun isNativeDarwin(name: String): Boolean { return listOf("ios", "macos", "tvos", "watchos").any { name.startsWith(it) } }

fun isNativeOther(name: String): Boolean { return listOf("linux", "mingw", "androidNative").any { name.startsWith(it) } }

defineSourceSet("concurrent", listOf("common")) { it in listOf("jvm", "native") }

if (project.nativeTargetsAreEnabled) {
    defineSourceSet("nativeDarwin", listOf("native")) { isNativeDarwin(it) }
    defineSourceSet("nativeOther", listOf("native")) { isNativeOther(it) }
}

/* ========================================================================== */


/*
 * All platform plugins and configuration magic happens here instead of build.gradle
 * because JMV-only projects depend on core, thus core should always be initialized before configuration.
 */
kotlin {
    /*
     * Configure two test runs:
     * 1) Main thread
     * 2) BG thread (required for Dispatchers.Main tests on Darwin)
     *
     * All new MM targets are build with optimize = true to have stress tests properly run.
     */
    targets.withType(KotlinNativeTargetWithTests::class).configureEach {
        binaries.getTest("DEBUG").apply {
            optimized = true
            // Test for memory leaks using a special entry point that does not exit but returns from main
            freeCompilerArgs = freeCompilerArgs + listOf("-e", "kotlinx.coroutines.mainNoExit")
        }

        binaries.test("workerTest", listOf(DEBUG)) {
            val thisTest = this
            optimized = true
            freeCompilerArgs = freeCompilerArgs + listOf("-e", "kotlinx.coroutines.mainBackground")
            testRuns.create("workerTest") {
                this as KotlinTaskTestRun<*, *>
                setExecutionSourceFrom(thisTest)
                executionTask.configure {
                    this as KotlinNativeTest
                    targetName = "$targetName worker with new MM"
                }
            }
        }
    }

    val jvmMain = sourceSets.jvmMain
    val jvmCoreMain = sourceSets.create("jvmCoreMain")
    val jdk8Main = sourceSets.create("jdk8Main")
    jdk8Main.dependsOn(jvmMain.get())

    /**
     * See: https://youtrack.jetbrains.com/issue/KTIJ-25959
     * The dependency from jvmCore to jvmMain is only for CLI builds and not intended for the IDE.
     * In the current setup there are two tooling unfriendly configurations used:
     * 1: - jvmMain, despite being a platform source set, is not a leaf (jvmCoreMain and jdk8Main dependOn it)
     * 2: - jvmMain effectively becomes a 'shared jvm' source set
     *
     * Using this kludge here, will prevent issue 2 from being visible to the IDE.
     * Therefore jvmMain will resolve using the 'single' compilation it participates in (from the perspective of the IDE)
     */
    if (!Idea.active) {
        jvmCoreMain.dependsOn(jvmMain.get())
    }

    jvm {
        val main = compilations.getByName("main")
        main.source(jvmCoreMain)
        main.source(jdk8Main)

        /* Create compilation for jvmCore to prove that jvmMain does not rely on jdk8 */
        compilations.create("CoreMain") {
            /* jvmCore is automatically matched as 'defaultSourceSet' for the compilation, due to its name */
            tasks.getByName("check").dependsOn(compileKotlinTaskProvider)
        }

        // For animal sniffer
        withJava()
        compilations.create("benchmark") { associateWith(compilations.getByName("main")) }
    }
}

benchmark {
    targets {
        register("jvmBenchmark")
    }
}

fun configureKotlinJvmPlatform(configuration: Configuration) {
    configuration.attributes.attribute(KotlinPlatformType.attribute, KotlinPlatformType.jvm)
}

// todo:KLUDGE: This is needed to workaround dependency resolution between Java and MPP modules
configurations {
    configureKotlinJvmPlatform(kotlinCompilerPluginClasspath.get())
}

// Update module name for metadata artifact to avoid conflicts
// see https://github.com/Kotlin/kotlinx.coroutines/issues/1797
val compileKotlinMetadata by tasks.getting(KotlinCompile::class) {
    kotlinOptions {
        freeCompilerArgs = freeCompilerArgs + listOf("-module-name", "kotlinx-coroutines-core-common")
    }
}

// :KLUDGE: Idea.active: This is needed to workaround resolve problems after importing this project to IDEA
fun configureNativeSourceSetPreset(name: String, preset: KotlinNativeTargetWithHostTestsPreset) {
    val hostMainCompilation = project.kotlin.targetFromPreset(preset).compilations.getByName("main")
    // Look for platform libraries in "implementation" for default source set
    val implementationConfiguration = configurations[hostMainCompilation.defaultSourceSet.implementationMetadataConfigurationName]
    // Now find the libraries: Finds platform libs & stdlib, but platform declarations are still not resolved due to IDE bugs
    val hostNativePlatformLibs = files(
        provider {
            implementationConfiguration.filter {
                it.path.endsWith(".klib") || it.absolutePath.contains("klib${File.separator}platform") || it.absolutePath.contains("stdlib")
            }
        }
    )
    // Add all those dependencies
    for (suffix in sourceSetSuffixes) {
        kotlin.sourceSets.getByName(name + suffix) {
            dependencies.add(implementationMetadataConfigurationName, hostNativePlatformLibs)
        }
    }
}

// :KLUDGE: Idea.active: Configure platform libraries for native source sets when working in IDEA
if (Idea.active && project.nativeTargetsAreEnabled) {
    val manager = project.ext["hostManager"] as HostManager
    val linuxPreset = kotlin.presets.getByName("linuxX64", KotlinNativeTargetWithHostTestsPreset::class)
    val macosPreset = kotlin.presets.getByName("macosX64", KotlinNativeTargetWithHostTestsPreset::class)
    // linux should be always available (cross-compilation capable) -- use it as default
    assert(manager.isEnabled(linuxPreset.konanTarget))
    // use macOS libs for nativeDarwin if available
    val macosAvailable = manager.isEnabled(macosPreset.konanTarget)
    // configure source sets
    configureNativeSourceSetPreset("native", linuxPreset)
    configureNativeSourceSetPreset("nativeOther", linuxPreset)
    configureNativeSourceSetPreset("nativeDarwin", if (macosAvailable) macosPreset else linuxPreset)
}

kotlin.sourceSets {
    val jvmMain by getting {
        dependencies {
            compileOnly("com.google.android:annotations:4.1.1.4")
        }
    }

    val jvmTest by getting {
        dependencies {
            api("org.jetbrains.kotlinx:lincheck:${version("lincheck")}")
            api("org.jetbrains.kotlinx:kotlinx-knit-test:${version("knit")}")
            implementation(project(":android-unit-tests"))
            implementation("org.openjdk.jol:jol-core:0.16")
        }
    }
}

kotlin.sourceSets.configureEach {
    // Do not apply 'ExperimentalForeignApi' where we have allWarningsAsErrors set
    if (name in listOf("jvmMain", "jvmCoreMain", "jsMain", "wasmJsMain", "jsAndWasmSharedMain", "concurrentMain", "commonMain")) return@configureEach
    languageSettings {
        optIn("kotlinx.cinterop.ExperimentalForeignApi")
        optIn("kotlin.experimental.ExperimentalNativeApi")
    }
}

val jvmTest by tasks.getting(Test::class) {
    minHeapSize = "1g"
    maxHeapSize = "1g"
    enableAssertions = true
    if (!Idea.active) {
        // We should not set this security manager when `jvmTest`
        // is invoked by IntelliJ IDEA since we need to pass
        // system properties for Lincheck and stress tests.
        // TODO Remove once IDEA is smart enough to select between `jvmTest`/`jvmStressTest`/`jvmLincheckTest` #KTIJ-599
        systemProperty("java.security.manager", "kotlinx.coroutines.TestSecurityManager")
    }
    // 'stress' is required to be able to run all subpackage tests like ":jvmTests --tests "*channels*" -Pstress=true"
    if (!Idea.active && rootProject.properties["stress"] == null) {
        exclude("**/*LincheckTest*")
        exclude("**/*StressTest.*")
    }
    if (Idea.active) {
        // Configure the IDEA runner for Lincheck
        configureJvmForLincheck(this)
    }
}

// Setup manifest for kotlinx-coroutines-core-jvm.jar
val jvmJar by tasks.getting(Jar::class) { setupManifest(this) }

/*
 * Setup manifest for kotlinx-coroutines-core.jar
 * This is convenient for users that pass -javaagent arg manually and also is a workaround #2619 and KTIJ-5659.
 * This manifest contains reference to AgentPremain that belongs to
 * kotlinx-coroutines-core-jvm, but our resolving machinery guarantees that
 * any JVM project that depends on -core artifact also depends on -core-jvm one.
 */
val allMetadataJar by tasks.getting(Jar::class) { setupManifest(this) }

fun setupManifest(jar: Jar) {
    jar.manifest {
        attributes(mapOf(
            "Premain-Class" to "kotlinx.coroutines.debug.AgentPremain",
            "Can-Retransform-Classes" to "true",
        ))
    }
}

val compileTestKotlinJvm by tasks.getting(KotlinJvmCompile::class)
val jvmTestClasses by tasks.getting

val jvmStressTest by tasks.registering(Test::class) {
    dependsOn(compileTestKotlinJvm)
    classpath = jvmTest.classpath
    testClassesDirs = jvmTest.testClassesDirs
    minHeapSize = "1g"
    maxHeapSize = "1g"
    include("**/*StressTest.*")
    enableAssertions = true
    testLogging.showStandardStreams = true
    systemProperty("kotlinx.coroutines.scheduler.keep.alive.sec", "100000") // any unpark problem hangs test
    // Adjust internal algorithmic parameters to increase the testing quality instead of performance.
    systemProperty("kotlinx.coroutines.semaphore.segmentSize", "1")
    systemProperty("kotlinx.coroutines.semaphore.maxSpinCycles", "10")
    systemProperty("kotlinx.coroutines.bufferedChannel.segmentSize", "2")
    systemProperty("kotlinx.coroutines.bufferedChannel.expandBufferCompletionWaitIterations", "1")
}

val jvmLincheckTest by tasks.registering(Test::class) {
    dependsOn(compileTestKotlinJvm)
    classpath = jvmTest.classpath
    testClassesDirs = jvmTest.testClassesDirs
    include("**/*LincheckTest*")
    enableAssertions = true
    testLogging.showStandardStreams = true
    configureJvmForLincheck(this)
}

// Additional Lincheck tests with `segmentSize = 2`.
// Some bugs cannot be revealed when storing one request per segment,
// and some are hard to detect when storing multiple requests.
val jvmLincheckTestAdditional by tasks.registering(Test::class) {
    dependsOn(compileTestKotlinJvm)
    classpath = jvmTest.classpath
    testClassesDirs = jvmTest.testClassesDirs
    include("**/RendezvousChannelLincheckTest*")
    include("**/Buffered1ChannelLincheckTest*")
    include("**/Semaphore*LincheckTest*")
    enableAssertions = true
    testLogging.showStandardStreams = true
    configureJvmForLincheck(this, true)
}

fun configureJvmForLincheck(task: Test, additional: Boolean = false) {
    task.minHeapSize = "1g"
    task.maxHeapSize = "4g" // we may need more space for building an interleaving tree in the model checking mode
    // https://github.com/JetBrains/lincheck#java-9
    task.jvmArgs = listOf("--add-opens", "java.base/jdk.internal.misc=ALL-UNNAMED",   // required for transformation
        "--add-exports", "java.base/sun.security.action=ALL-UNNAMED",
        "--add-exports", "java.base/jdk.internal.util=ALL-UNNAMED") // in the model checking mode
    // Adjust internal algorithmic parameters to increase the testing quality instead of performance.
    val segmentSize = if (additional) "2" else "1"
    task.systemProperty("kotlinx.coroutines.semaphore.segmentSize", segmentSize)
    task.systemProperty("kotlinx.coroutines.semaphore.maxSpinCycles", "1") // better for the model checking mode
    task.systemProperty("kotlinx.coroutines.bufferedChannel.segmentSize", segmentSize)
    task.systemProperty("kotlinx.coroutines.bufferedChannel.expandBufferCompletionWaitIterations", "1")
}

// Always check additional test sets
val moreTest by tasks.registering {
    dependsOn(listOf(jvmStressTest, jvmLincheckTest, jvmLincheckTestAdditional))
}

val check by tasks.getting {
    dependsOn(moreTest)
}

kover {
    excludeTests {
        // Always disabled, lincheck doesn't really support coverage
        tasks("jvmLincheckTest")
    }

    excludeInstrumentation {
        // lincheck has NPE error on `ManagedStrategyStateHolder` class
        classes("org.jetbrains.kotlinx.lincheck.*")
    }
}

koverReport {
    filters {
        excludes {
            classes(
                "kotlinx.coroutines.debug.*", // Tested by debug module
                "kotlinx.coroutines.channels.ChannelsKt__DeprecatedKt*", // Deprecated
                "kotlinx.coroutines.scheduling.LimitingDispatcher", // Deprecated
                "kotlinx.coroutines.scheduling.ExperimentalCoroutineDispatcher", // Deprecated
                "kotlinx.coroutines.flow.FlowKt__MigrationKt*", // Migrations
                "kotlinx.coroutines.flow.LintKt*", // Migrations
                "kotlinx.coroutines.internal.WeakMapCtorCache", // Fallback implementation that we never test
                "_COROUTINE._CREATION", // For IDE navigation
                "_COROUTINE._BOUNDARY", // For IDE navigation
            )
        }
    }
}

val testsJar by tasks.registering(Jar::class) {
    dependsOn(jvmTestClasses)
    archiveClassifier = "tests"
    from(compileTestKotlinJvm.destinationDirectory)
}

artifacts {
    archives(testsJar)
}

// Workaround for https://github.com/Kotlin/dokka/issues/1833: make implicit dependency explicit
tasks.named("dokkaHtmlPartial") {
    dependsOn(jvmJar)
}
