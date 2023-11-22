import com.github.jengelman.gradle.plugins.shadow.tasks.*

/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

apply(plugin = "com.github.johnrengelman.shadow")

// apply plugin to use autocomplete for Kover DSL
apply(plugin = "org.jetbrains.kotlinx.kover")

configurations {
    val shadowDeps by creating // shaded dependencies, not included into the resulting .pom file
    compileOnly.get().extendsFrom(shadowDeps)
    runtimeOnly.get().extendsFrom(shadowDeps)
}

val junit_version by properties
val junit5_version by properties
val byte_buddy_version by properties
val blockhound_version by properties
val jna_version by properties

dependencies {
    compileOnly("junit:junit:$junit_version")
    compileOnly("org.junit.jupiter:junit-jupiter-api:$junit5_version")
    testImplementation("org.junit.jupiter:junit-jupiter-engine:$junit5_version")
    testImplementation("org.junit.platform:junit-platform-testkit:1.7.0")
    add("shadowDeps", "net.bytebuddy:byte-buddy:$byte_buddy_version")
    add("shadowDeps", "net.bytebuddy:byte-buddy-agent:$byte_buddy_version")
    compileOnly("io.projectreactor.tools:blockhound:$blockhound_version")
    testImplementation("io.projectreactor.tools:blockhound:$blockhound_version")
    testImplementation("com.google.code.gson:gson:2.8.6")
    api("net.java.dev.jna:jna:$jna_version")
    api("net.java.dev.jna:jna-platform:$jna_version")
}

java {
    /* This is needed to be able to run JUnit5 tests. Otherwise, Gradle complains that it can't find the
    JVM1.6-compatible version of the `junit-jupiter-api` artifact. */
    disableAutoTargetJvm()
}

// This is required for BlockHound tests to work, see https://github.com/Kotlin/kotlinx.coroutines/issues/3701
tasks.withType<Test>().configureEach {
    if (JavaVersion.current().isCompatibleWith(JavaVersion.VERSION_13)) {
        jvmArgs("-XX:+AllowRedefinitionToAddDeleteMethods")
    }
}

val jar by tasks.getting(Jar::class) {
    enabled = false
}

val shadowJar by tasks.getting(ShadowJar::class) {
    // Shadow only byte buddy, do not package kotlin stdlib
    configurations = listOf(project.configurations["shadowDeps"])
    relocate("net.bytebuddy", "kotlinx.coroutines.repackaged.net.bytebuddy")
    // exclude the module-info.class provided by bytebuddy
    exclude("META-INF/versions/9/module-info.class")
}

// adapted from <https://github.com/johnrengelman/shadow/issues/710#issuecomment-1280585784>
// There doesn't seem to be a way to ask the shadow jar to contain the `module-info.class` provided by us and not
// the one provided by bytebuddy. So, this is done in two steps: `shadowJarTask` excludes the module-info from
// bytebuddy, and this task creates another jar file, this time one that has the correct module-info.
val shadowJarWithCorrectModuleInfo by tasks.registering(Jar::class) {
    group = "shadow"
    from(zipTree(shadowJar.archiveFile))
    from(tasks.compileModuleInfoJava) {
        // Include **only** file we are interested in as JavaCompile output also contains some tmp files
        include("module-info.class")
        into("META-INF/versions/9/")
    }
    duplicatesStrategy = DuplicatesStrategy.FAIL
    archiveBaseName.set(jar.archiveBaseName)
    archiveVersion.set(jar.archiveVersion)
    archiveClassifier.set(jar.archiveClassifier)
    manifest {
        attributes(mapOf(
            "Premain-Class" to "kotlinx.coroutines.debug.AgentPremain",
            "Can-Redefine-Classes" to "true",
            "Multi-Release" to "true"
        ))
    }
}

tasks.getByName("publishMavenPublicationToMavenLocal") {
    dependsOn(shadowJarWithCorrectModuleInfo)
}

VersionFile.configure(project, shadowJarWithCorrectModuleInfo.get())

configurations.all {
    outgoing.artifacts.removeIf {
        val dependencies = it.buildDependencies.getDependencies(null)
        dependencies.contains(jar) || dependencies.contains(shadowJar)
    }
    if (name == "apiElements" || name == "runtimeElements") {
        outgoing.artifact(shadowJarWithCorrectModuleInfo)
    }
}

koverReport {
    filters {
        excludes {
            // Never used, safety mechanism
            classes("kotlinx.coroutines.debug.internal.NoOpProbesKt")
        }
    }
}
