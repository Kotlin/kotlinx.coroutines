import org.gradle.api.JavaVersion
import org.gradle.api.tasks.bundling.Jar
import org.gradle.api.tasks.testing.Test

plugins {
    id("org.jetbrains.kotlinx.kover") // apply plugin to use autocomplete for Kover DSL
}

val junitVersion = providers.gradleProperty("junit_version").get()
val junit5Version = providers.gradleProperty("junit5_version").get()
val byteBuddyVersion = providers.gradleProperty("byte_buddy_version").get()
val blockhoundVersion = providers.gradleProperty("blockhound_version").get()
val jnaVersion = providers.gradleProperty("jna_version").get()

dependencies {
    compileOnly("junit:junit:$junitVersion")
    compileOnly("org.junit.jupiter:junit-jupiter-api:$junit5Version")
    testImplementation("org.junit.jupiter:junit-jupiter-engine:$junit5Version")
    testImplementation("org.junit.platform:junit-platform-testkit:1.7.0")
    implementation("net.bytebuddy:byte-buddy:$byteBuddyVersion")
    implementation("net.bytebuddy:byte-buddy-agent:$byteBuddyVersion")
    compileOnly("io.projectreactor.tools:blockhound:$blockhoundVersion")
    testImplementation("io.projectreactor.tools:blockhound:$blockhoundVersion")
    testImplementation("com.google.code.gson:gson:2.8.6")
    api("net.java.dev.jna:jna:$jnaVersion")
    api("net.java.dev.jna:jna-platform:$jnaVersion")
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
