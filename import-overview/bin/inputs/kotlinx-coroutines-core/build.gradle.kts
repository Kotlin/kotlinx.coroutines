import org.gradle.api.tasks.testing.*
import org.gradle.kotlin.dsl.*
import org.gradle.kotlin.dsl.withType
import org.jetbrains.dokka.gradle.tasks.DokkaBaseTask
import org.jetbrains.kotlin.gradle.tasks.*
import ru.vyarus.gradle.plugin.animalsniffer.AnimalSniffer

plugins {
    kotlin("jvm")
    id("org.jetbrains.kotlinx.benchmark")
    id("org.jetbrains.dokka")
    id("org.jetbrains.kotlinx.kover")
}

apply(plugin = "pub-conventions")

dependencies {
    compileOnly("com.google.android:annotations:4.1.1.4")
    testImplementation("org.jetbrains.kotlinx:lincheck:${version("lincheck")}")
    testImplementation("org.jetbrains.kotlinx:kotlinx-knit-test:${version("knit")}")
    testImplementation(project(":android-unit-tests"))
    testImplementation("org.openjdk.jol:jol-core:0.16")
}

val benchmarkSourceSet = sourceSets.create("benchmark")
kotlin {
    sourceSets.named("benchmark") {
        kotlin.srcDirs("benchmarks/main/kotlin", "benchmarks/jvm/kotlin")
    }
    target.compilations.named("benchmark") {
        associateWith(target.compilations.getByName("main"))
    }
    // Keep the module name stable for coroutine debugger access to internal symbols.
    compilerOptions.moduleName = project.name
}
dependencies {
    add(benchmarkSourceSet.implementationConfigurationName,
        "org.jetbrains.kotlinx:kotlinx-benchmark-runtime:${version("benchmarks")}")
}
benchmark {
    targets.register("benchmark")
}

val jvmTest = tasks.getByName<Test>("test") {
    minHeapSize = "1g"
    maxHeapSize = "1g"
    enableAssertions = true
    // 'stress' is required to be able to run all subpackage tests like ":test --tests "*channels*" -Pstress=true"
    if (!Idea.active && !providers.gradleProperty("stress").isPresent) {
        exclude("**/*LincheckTest*")
        exclude("**/*StressTest.*")
    }
    if (Idea.active) {
        // Configure the IDEA runner for Lincheck
        configureJvmForLincheck()
    }
}

val jvmJar = tasks.getByName<Jar>("jar") { setupManifest(this) }

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

val compileTestKotlin = tasks.getByName<KotlinJvmCompile>("compileTestKotlin")

val jvmStressTest = tasks.register<Test>("jvmStressTest") {
    dependsOn(compileTestKotlin)
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

val jvmLincheckTest = tasks.register<Test>("jvmLincheckTest") {
    dependsOn(compileTestKotlin)
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
val jvmLincheckTestAdditional = tasks.register<Test>("jvmLincheckTestAdditional") {
    dependsOn(compileTestKotlin)
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
    // Fails with an exception in the model checking mode without these arguments for Java 9+:
    jvmArgs = listOf(
        "--add-opens", "java.base/jdk.internal.misc=ALL-UNNAMED",   // required for transformation
        "--add-exports", "java.base/jdk.internal.util=ALL-UNNAMED"
    )
    // Adjust internal algorithmic parameters to increase the testing quality instead of performance.
    systemProperty("kotlinx.coroutines.semaphore.segmentSize", segmentSize)
    systemProperty("kotlinx.coroutines.semaphore.maxSpinCycles", 1) // better for the model checking mode
    systemProperty("kotlinx.coroutines.bufferedChannel.segmentSize", segmentSize)
    systemProperty("kotlinx.coroutines.bufferedChannel.expandBufferCompletionWaitIterations", 1)
}

// Always check additional test sets
val moreTest = tasks.register("moreTest") {
    dependsOn(listOf(jvmStressTest, jvmLincheckTest, jvmLincheckTestAdditional))
}

val check = tasks.getByName("check") {
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

// Workaround for https://github.com/Kotlin/dokka/issues/1833: make implicit dependency explicit
tasks.withType<DokkaBaseTask>() {
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
    defaultTargets = setOf("main")
}
