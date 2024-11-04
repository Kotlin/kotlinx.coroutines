import org.gradle.api.JavaVersion
import org.gradle.api.file.DuplicatesStrategy
import org.gradle.api.tasks.bundling.Jar
import org.gradle.api.tasks.testing.Test

plugins {
    id("org.jetbrains.kotlinx.kover") // apply plugin to use autocomplete for Kover DSL
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
    implementation("net.bytebuddy:byte-buddy:$byte_buddy_version")
    implementation("net.bytebuddy:byte-buddy-agent:$byte_buddy_version")
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

tasks.named<Jar>("jar") {
    manifest {
        attributes(
            mapOf(
                "Premain-Class" to "kotlinx.coroutines.debug.internal.AgentPremain",
                "Can-Redefine-Classes" to "true",
                "Multi-Release" to "true"
            )
        )
    }

    // add module-info.class to the META-INF/versions/9/ directory.
    dependsOn(tasks.compileModuleInfoJava)
    from(tasks.compileModuleInfoJava.get().outputs.files.asFileTree.matching {
        include("module-info.class")
    }) {
        this.duplicatesStrategy = DuplicatesStrategy.INCLUDE
        into("META-INF/versions/9")
    }
}


kover {
    reports {
        filters {
            excludes {
                // Never used, safety mechanism
                classes("kotlinx.coroutines.debug.NoOpProbesKt")
            }
        }
    }
}
