import org.gradle.api.tasks.testing.*
import org.gradle.kotlin.dsl.*
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension
import org.jetbrains.kotlin.gradle.plugin.KotlinSourceSet
import org.jetbrains.kotlin.gradle.plugin.mpp.*
import org.jetbrains.kotlin.gradle.targets.native.tasks.*
import org.jetbrains.kotlin.gradle.tasks.*
import org.jetbrains.kotlin.gradle.testing.*
import ru.vyarus.gradle.plugin.animalsniffer.AnimalSniffer

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
     ------------------------------------------------------------
     wasmJs \------> jsAndWasmJsShared ----+
     js     /                              |
                                           V
     wasmWasi --------------------> jsAndWasmShared ----------+
                                                              |
                                                              V
     jvm ----------------------------> concurrent -------> common
                                        ^
     ios     \                          |
     macos   | ---> nativeDarwin ---> native ---+
     tvos    |                         ^
     watchos /                         |
                                       |
     linux  \  ---> nativeOther -------+
     mingw  /
 ========================================================================== */

kotlin {
    sourceSets {
        // using the source set names from <https://kotlinlang.org/docs/multiplatform-hierarchy.html#see-the-full-hierarchy-template>
        groupSourceSets("concurrent", listOf("jvm", "native"), listOf("common"))
        if (project.nativeTargetsAreEnabled) {
            // TODO: 'nativeDarwin' behaves exactly like 'apple', we can remove it
            groupSourceSets("nativeDarwin", listOf("apple"), listOf("native"))
            groupSourceSets("nativeOther", listOf("linux", "mingw", "androidNative"), listOf("native"))
        }
        jvmMain {
            dependencies {
                compileOnly("com.google.android:annotations:4.1.1.4")
            }
        }
        jvmTest {
            dependencies {
                api("org.jetbrains.kotlinx:lincheck:${version("lincheck")}")
                api("org.jetbrains.kotlinx:kotlinx-knit-test:${version("knit")}")
                implementation(project(":android-unit-tests"))
                implementation("org.openjdk.jol:jol-core:0.16")
            }
        }
    }
    setupBenchmarkSourceSets(sourceSets)

    /*
     * Configure two test runs for Native:
     * 1) Main thread
     * 2) BG thread (required for Dispatchers.Main tests on Darwin)
     *
     * All new MM targets are build with optimize = true to have stress tests properly run.
     */
    targets.withType(KotlinNativeTargetWithTests::class).configureEach {
        binaries.test("workerTest", listOf(DEBUG)) {
            val thisTest = this
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
}

private fun KotlinMultiplatformExtension.setupBenchmarkSourceSets(ss: NamedDomainObjectContainer<KotlinSourceSet>) {
    // Forgive me, Father, for I have sinned.
    // Really, that is needed to have benchmark sourcesets be the part of the project, not a separate project
    val benchmarkMain by ss.creating {
        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-benchmark-runtime:${version("benchmarks")}")
        }
        // For each source set we have to manually set path to the sources, otherwise lookup will fail
        kotlin.srcDir("benchmarks/main/kotlin")
    }

    @Suppress("UnusedVariable")
    val jvmBenchmark by ss.creating {
        // For each source set we have to manually set path to the sources, otherwise lookup will fail
        kotlin.srcDir("benchmarks/jvm/kotlin")
    }

    targets.matching {
        it.name != "metadata"
            // Doesn't work, don't want to figure it out for now
            && !it.name.contains("wasm")
            && !it.name.contains("js")
    }.all {
        compilations.create("benchmark") {
            associateWith(this@all.compilations.getByName("main"))
            defaultSourceSet {
                dependencies {
                    implementation("org.jetbrains.kotlinx:kotlinx-benchmark-runtime:${version("benchmarks")}")
                }
                dependsOn(benchmarkMain)
            }
        }
    }

    targets.matching { it.name != "metadata" }.all {
        benchmark.targets.register("${name}Benchmark")
    }
}

// Update module name for metadata artifact to avoid conflicts
// see https://github.com/Kotlin/kotlinx.coroutines/issues/1797
val compileKotlinMetadata by tasks.getting(KotlinCompilationTask::class) {
    compilerOptions {
        freeCompilerArgs.addAll("-module-name", "kotlinx-coroutines-core-common")
    }
}

val jvmTest by tasks.getting(Test::class) {
    minHeapSize = "1g"
    maxHeapSize = "1g"
    enableAssertions = true
    // 'stress' is required to be able to run all subpackage tests like ":jvmTests --tests "*channels*" -Pstress=true"
    if (!Idea.active && rootProject.properties["stress"] == null) {
        exclude("**/*LincheckTest*")
        exclude("**/*StressTest.*")
    }
    if (Idea.active) {
        // Configure the IDEA runner for Lincheck
        configureJvmForLincheck()
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
        attributes(
            mapOf(
                "Premain-Class" to "kotlinx.coroutines.debug.internal.AgentPremain",
                "Can-Retransform-Classes" to "true",
            )
        )
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
    systemProperty("kotlinx.coroutines.scheduler.keep.alive.sec", 100000) // any unpark problem hangs test
    // Adjust internal algorithmic parameters to increase the testing quality instead of performance.
    systemProperty("kotlinx.coroutines.semaphore.segmentSize", 1)
    systemProperty("kotlinx.coroutines.semaphore.maxSpinCycles", 10)
    systemProperty("kotlinx.coroutines.bufferedChannel.segmentSize", 2)
    systemProperty("kotlinx.coroutines.bufferedChannel.expandBufferCompletionWaitIterations", 1)
}

val jvmLincheckTest by tasks.registering(Test::class) {
    dependsOn(compileTestKotlinJvm)
    classpath = jvmTest.classpath
    testClassesDirs = jvmTest.testClassesDirs
    include("**/*LincheckTest*")
    enableAssertions = true
    testLogging.showStandardStreams = true
    configureJvmForLincheck()
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
    configureJvmForLincheck(segmentSize = 2)
}

fun Test.configureJvmForLincheck(segmentSize: Int = 1) {
    minHeapSize = "1g"
    maxHeapSize = "4g" // we may need more space for building an interleaving tree in the model checking mode
    // https://github.com/JetBrains/lincheck#java-9
    jvmArgs = listOf(
        "--add-opens", "java.base/jdk.internal.misc=ALL-UNNAMED",   // required for transformation
        "--add-exports", "java.base/sun.security.action=ALL-UNNAMED",
        "--add-exports", "java.base/jdk.internal.util=ALL-UNNAMED"
    ) // in the model checking mode
    // Adjust internal algorithmic parameters to increase the testing quality instead of performance.
    systemProperty("kotlinx.coroutines.semaphore.segmentSize", segmentSize)
    systemProperty("kotlinx.coroutines.semaphore.maxSpinCycles", 1) // better for the model checking mode
    systemProperty("kotlinx.coroutines.bufferedChannel.segmentSize", segmentSize)
    systemProperty("kotlinx.coroutines.bufferedChannel.expandBufferCompletionWaitIterations", 1)
}

// Always check additional test sets
val moreTest by tasks.registering {
    dependsOn(listOf(jvmStressTest, jvmLincheckTest, jvmLincheckTestAdditional))
}

val check by tasks.getting {
    dependsOn(moreTest)
}

kover {
    currentProject {
        instrumentation {
            // Always disabled, lincheck doesn't really support coverage
            disabledForTestTasks.addAll("jvmLincheckTest")

            // lincheck has NPE error on `ManagedStrategyStateHolder` class
            excludedClasses.addAll("org.jetbrains.kotlinx.lincheck.*")
        }
        sources {
            excludedSourceSets.addAll("benchmark")
        }
    }

    reports {
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

// Specific files so nothing from core is accidentally skipped
tasks.withType<AnimalSniffer> {
    exclude("**/future/FutureKt*")
    exclude("**/future/ContinuationHandler*")
    exclude("**/future/CompletableFutureCoroutine*")

    exclude("**/stream/StreamKt*")
    exclude("**/stream/StreamFlow*")

    exclude("**/time/TimeKt*")
}

animalsniffer {
    defaultTargets = setOf("jvmMain")
}
