import com.github.jengelman.gradle.plugins.shadow.tasks.*
import java.net.*
import java.nio.file.*

plugins {
    id("com.github.johnrengelman.shadow")
    id("org.jetbrains.kotlinx.kover") // apply plugin to use autocomplete for Kover DSL
}

configurations {
    val shadowDeps by creating
    compileOnly.configure {
        extendsFrom(shadowDeps)
    }
    runtimeOnly.configure {
        extendsFrom(shadowDeps)
    }
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
    if (JavaVersion.toVersion(jdkToolchainVersion).isCompatibleWith(JavaVersion.VERSION_13)) {
        jvmArgs("-XX:+AllowRedefinitionToAddDeleteMethods")
    }
}

val jar by tasks.existing(Jar::class) {
    enabled = false
}

val shadowJar by tasks.existing(ShadowJar::class) {
    // Shadow only byte buddy, do not package kotlin stdlib
    configurations = listOf(project.configurations["shadowDeps"])
    relocate("net.bytebuddy", "kotlinx.coroutines.repackaged.net.bytebuddy")
    /* These classifiers are both set to `null` to trick Gradle into thinking that this jar file is both the
    artifact from the `jar` task and the one from `shadowJar`. Without this, Gradle complains that the artifact
    from the `jar` task is not present when the compilaton finishes, even if the file with this name exists. */
    archiveClassifier.convention(null as String?)
    archiveClassifier = null
    archiveBaseName = jar.flatMap { it.archiveBaseName }
    archiveVersion = jar.flatMap { it.archiveVersion }
    manifest {
        attributes(
            mapOf(
                "Premain-Class" to "kotlinx.coroutines.debug.AgentPremain",
                "Can-Redefine-Classes" to "true",
                "Multi-Release" to "true"
            )
        )
    }
    // add module-info.class to the META-INF/versions/9/ directory.
    dependsOn(tasks.compileModuleInfoJava)
    doLast {
        // We can't do that directly with the shadowJar task because it doesn't support replacing existing files.
        val zipPath = this@existing.outputs.files.singleFile.toPath()
        val zipUri = URI.create("jar:${zipPath.toUri()}")
        val moduleInfoFilePath = tasks.compileModuleInfoJava.get().outputs.files.asFileTree.matching {
            include("module-info.class")
        }.singleFile.toPath()
        FileSystems.newFileSystem(zipUri, emptyMap<String, String>()).use { fs ->
            val moduleInfoFile = fs.getPath("META-INF/versions/9/module-info.class")
            Files.copy(moduleInfoFilePath, moduleInfoFile, StandardCopyOption.REPLACE_EXISTING)
        }
    }
}

configurations {
    // shadowJar is already part of the `shadowRuntimeElements` and `shadowApiElements`, but the other subprojects
    // that depend on `kotlinx-coroutines-debug` look at `runtimeElements` and `apiElements`.
    artifacts {
        add("apiElements", shadowJar)
        add("runtimeElements", shadowJar)
    }
}

kover {
    reports {
        filters {
            excludes {
                // Never used, safety mechanism
                classes("kotlinx.coroutines.debug.internal.NoOpProbesKt")
            }
        }
    }
}
