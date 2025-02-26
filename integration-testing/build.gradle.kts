import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile
import org.jetbrains.kotlin.gradle.targets.js.npm.tasks.KotlinNpmInstallTask
import org.jetbrains.kotlin.gradle.dsl.jvm.JvmTargetValidationMode

buildscript {
    /*
        These property group is used to build kotlinx.coroutines against Kotlin compiler snapshot.
        How does it work:
        When build_snapshot_train is set to true, kotlin_version property is overridden with kotlin_snapshot_version,
        atomicfu_version is overwritten by TeamCity environment (AFU is built with snapshot and published to mavenLocal
        as previous step or the snapshot build).
        Additionally, mavenLocal and Sonatype snapshots are added to repository list and stress tests are disabled.
        DO NOT change the name of these properties without adapting kotlinx.train build chain.
    */
    fun checkIsSnapshotTrainProperty(): Boolean {
        val buildSnapshotTrain = providers.gradleProperty("build_snapshot_train").orNull
        return !buildSnapshotTrain.isNullOrEmpty()
    }

    val firstPartyDependencies = listOf(
        "kotlin",
        "atomicfu",
    )

    fun checkIsSnapshotVersion(): Boolean {
        var usingSnapshotVersion = checkIsSnapshotTrainProperty()
        for (key in firstPartyDependencies) {
            val value = providers.gradleProperty("${key}_version").orNull
                ?.takeIf { it.endsWith("-SNAPSHOT") }
                ?: continue
            println("NOTE: USING SNAPSHOT VERSION: $key=$value")
            usingSnapshotVersion = true
        }
        return usingSnapshotVersion
    }

    val usingSnapshotVersion = checkIsSnapshotVersion()
    val hasSnapshotTrainProperty = checkIsSnapshotTrainProperty()

    extra.apply {
        set("using_snapshot_version", usingSnapshotVersion)
        set("build_snapshot_train", hasSnapshotTrainProperty)
    }

    if (usingSnapshotVersion) {
        repositories {
            mavenLocal()
            maven("https://redirector.kotlinlang.org/maven/dev")
            maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        }
    }
}

plugins {
    id("org.jetbrains.kotlin.jvm") version extra["kotlin_version"].toString()
}

repositories {
    if (extra["using_snapshot_version"] == true) {
        maven("https://redirector.kotlinlang.org/maven/dev")
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
    }
    mavenLocal()
    maven("https://redirector.kotlinlang.org/maven/dev")
    mavenCentral()
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

val kotlinVersion = if (extra["build_snapshot_train"] == true) {
    providers.gradleProperty("kotlin_snapshot_version").orNull
        ?: throw IllegalArgumentException("'kotlin_snapshot_version' should be defined when building with snapshot compiler")
} else {
    providers.gradleProperty("kotlin_version").get()
}

val asmVersion = property("asm_version")

dependencies {
    testImplementation("org.jetbrains.kotlin:kotlin-test:$kotlinVersion")
    testImplementation("org.ow2.asm:asm:$asmVersion")
    implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
}

val coroutinesVersion = property("coroutines_version").toString()

sourceSets {
    // An assortment of tests for behavior of the core coroutines module on JVM
    create("jvmCoreTest") {
        compileClasspath += sourceSets.test.get().runtimeClasspath
        runtimeClasspath += sourceSets.test.get().runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
            implementation("com.google.guava:guava:31.1-jre")
        }
    }

    // Checks correctness of Maven publication (JAR resources) and absence of atomicfu symbols
    create("mavenTest") {
        compileClasspath += sourceSets.test.get().runtimeClasspath
        runtimeClasspath += sourceSets.test.get().runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-android:$coroutinesVersion")
        }
    }

    // Checks that kotlinx-coroutines-debug can be used as -javaagent parameter
    create("debugAgentTest") {
        compileClasspath += sourceSets.test.get().runtimeClasspath
        runtimeClasspath += sourceSets.test.get().runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:$coroutinesVersion")
        }
    }

    // Checks that kotlinx-coroutines-debug agent can self-attach dynamically to JVM as a standalone dependency
    create("debugDynamicAgentTest") {
        compileClasspath += sourceSets.test.get().runtimeClasspath
        runtimeClasspath += sourceSets.test.get().runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:$coroutinesVersion")
        }
    }

    // Checks that kotlinx-coroutines-core can be used as -javaagent parameter
    create("coreAgentTest") {
        compileClasspath += sourceSets.test.get().runtimeClasspath
        runtimeClasspath += sourceSets.test.get().runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
        }
    }

    create("javaConsumersTest") {
        compileClasspath += sourceSets.test.get().runtimeClasspath
        runtimeClasspath += sourceSets.test.get().runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
        }
    }
}

kotlin {
    jvmToolchain(17)

    compilerOptions {
        jvmTarget.set(JvmTarget.JVM_17)
    }
}

tasks {
    named<KotlinCompile>("compileDebugAgentTestKotlin") {
        compilerOptions {
            freeCompilerArgs.add("-Xallow-kotlin-package")
            jvmTarget.set(JvmTarget.JVM_1_8)
        }
    }

    named<KotlinCompile>("compileTestKotlin") {
        compilerOptions {
            jvmTarget.set(JvmTarget.JVM_17)
        }
    }

    create<Test>("jvmCoreTest") {
        environment("version", coroutinesVersion)
        val sourceSet = sourceSets[name]
        testClassesDirs = sourceSet.output.classesDirs
        classpath = sourceSet.runtimeClasspath
    }

    create<Test>("mavenTest") {
        environment("version", coroutinesVersion)
        val sourceSet = sourceSets[name]
        testClassesDirs = sourceSet.output.classesDirs
        classpath = sourceSet.runtimeClasspath
    }

    create<Test>("debugAgentTest") {
        val sourceSet = sourceSets[name]
        val coroutinesDebugJar = sourceSet.runtimeClasspath.filter {
            it.name == "kotlinx-coroutines-debug-$coroutinesVersion.jar"
        }.singleFile
        jvmArgs("-javaagent:$coroutinesDebugJar")
        testClassesDirs = sourceSet.output.classesDirs
        classpath = sourceSet.runtimeClasspath
        systemProperties["overwrite.probes"] = project.properties["overwrite.probes"]
    }

    create<Test>("debugDynamicAgentTest") {
        val sourceSet = sourceSets[name]
        testClassesDirs = sourceSet.output.classesDirs
        classpath = sourceSet.runtimeClasspath
    }

    create<Test>("coreAgentTest") {
        val sourceSet = sourceSets[name]
        val coroutinesDebugJar = sourceSet.runtimeClasspath.filter {
            it.name == "kotlinx-coroutines-core-jvm-$coroutinesVersion.jar"
        }.singleFile
        jvmArgs("-javaagent:$coroutinesDebugJar")
        testClassesDirs = sourceSet.output.classesDirs
        classpath = sourceSet.runtimeClasspath
    }

    create<Test>("javaConsumersTest") {
        val sourceSet = sourceSets[name]
        testClassesDirs = sourceSet.output.classesDirs
        classpath = sourceSet.runtimeClasspath
    }

    check {
        dependsOn(
            "jvmCoreTest",
            "debugDynamicAgentTest",
            "mavenTest",
            "debugAgentTest",
            "coreAgentTest",
            "javaConsumersTest",
            ":jpmsTest:check",
            "smokeTest:build",
            "java8Test:check",
        )
    }

    // Drop this when node js version become stable
    withType(KotlinNpmInstallTask::class.java).configureEach {
        args.add("--ignore-engines")
    }

    withType(KotlinJvmCompile::class.java).configureEach {
        jvmTargetValidationMode = JvmTargetValidationMode.WARNING
    }
}
