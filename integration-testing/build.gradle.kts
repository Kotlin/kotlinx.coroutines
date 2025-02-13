import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

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
        val buildSnapshotTrain = rootProject.properties["build_snapshot_train"]?.toString()
        return !buildSnapshotTrain.isNullOrEmpty()
    }

    fun checkIsSnapshotVersion(): Boolean {
        var usingSnapshotVersion = checkIsSnapshotTrainProperty()
        rootProject.properties.forEach { (key, value) ->
            if (key.endsWith("_version") && value is String && value.endsWith("-SNAPSHOT")) {
                println("NOTE: USING SNAPSHOT VERSION: $key=$value")
                usingSnapshotVersion = true
            }
        }
        return usingSnapshotVersion
    }

    fun fetchKotlinVersion(): String {
        if (checkIsSnapshotTrainProperty()) {
            val kotlinSnapshotVersion = rootProject.properties["kotlin_snapshot_version"]?.toString()
                ?: throw IllegalArgumentException("'kotlin_snapshot_version' should be defined when building with snapshot compiler")
            return kotlinSnapshotVersion
        }
        return rootProject.properties["kotlin_version"].toString()
    }

    val isEnabledNativeTargets = rootProject.properties["disable_native_targets"] == null
    val usingSnapshotVersion = checkIsSnapshotVersion()
    val hasSnapshotTrainProperty = checkIsSnapshotTrainProperty()
    val kotlinVersion = fetchKotlinVersion()

    extra.apply {
        set("native_targets_enabled", isEnabledNativeTargets)
        set("using_snapshot_version", usingSnapshotVersion)
        set("build_snapshot_train", hasSnapshotTrainProperty)
        set("kotlin_version", kotlinVersion)
    }

    if (usingSnapshotVersion) {
        repositories {
            mavenLocal()
            maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        }
    }
}

plugins {
    id("org.jetbrains.kotlin.jvm") version "2.0.0"
}

repositories {
    if (extra["using_snapshot_version"] == true) {
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
    }
    mavenLocal()
    mavenCentral()
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

val kotlinVersion = extra["kotlin_version"]
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
}

kotlin {
    jvmToolchain(17)

    compilerOptions {
        jvmTarget.set(JvmTarget.JVM_17)
    }
}

tasks.named<KotlinCompile>("compileDebugAgentTestKotlin") {
    compilerOptions {
        freeCompilerArgs.add("-Xallow-kotlin-package")
        jvmTarget.set(JvmTarget.JVM_1_8)
    }
}

tasks.named<KotlinCompile>("compileTestKotlin") {
    compilerOptions {
        jvmTarget.set(JvmTarget.JVM_17)
    }
}

tasks.create<Test>("jvmCoreTest") {
    environment("version", coroutinesVersion)
    val sourceSet = sourceSets.getByName("jvmCoreTest")
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

tasks.create<Test>("mavenTest") {
    environment("version", coroutinesVersion)
    val sourceSet = sourceSets.getByName("mavenTest")
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

tasks.create<Test>("debugAgentTest") {
    val sourceSet = sourceSets["debugAgentTest"]
    val coroutinesDebugJar = sourceSet.runtimeClasspath.filter {
        it.name == "kotlinx-coroutines-debug-$coroutinesVersion.jar"
    }.singleFile
    jvmArgs("-javaagent:$coroutinesDebugJar")
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
    systemProperties["overwrite.probes"] = project.properties["overwrite.probes"]
}

tasks.create<Test>("debugDynamicAgentTest") {
    val sourceSet = sourceSets["debugDynamicAgentTest"]
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

tasks.create<Test>("coreAgentTest") {
    val sourceSet = sourceSets["coreAgentTest"]
    val coroutinesDebugJar = sourceSet.runtimeClasspath.filter {
        it.name == "kotlinx-coroutines-core-jvm-$coroutinesVersion.jar"
    }.singleFile
    jvmArgs("-javaagent:$coroutinesDebugJar")
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

tasks.check {
    dependsOn(
        "jvmCoreTest",
        "debugDynamicAgentTest",
        "mavenTest",
        "debugAgentTest",
        "coreAgentTest",
        ":jpmsTest:check",
        "smokeTest:build",
        "java8Test:check"
    )
}

// Drop this when node js version become stable
tasks.withType(org.jetbrains.kotlin.gradle.targets.js.npm.tasks.KotlinNpmInstallTask::class.java).configureEach {
    args.add("--ignore-engines")
}

tasks.withType(org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile::class.java).configureEach {
    jvmTargetValidationMode = org.jetbrains.kotlin.gradle.dsl.jvm.JvmTargetValidationMode.WARNING
}