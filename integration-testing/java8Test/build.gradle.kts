plugins {
    kotlin("jvm")
}

repositories {
    mavenCentral()
    maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
    maven("https://redirector.kotlinlang.org/maven/dev")
    // Coroutines from the outer project are published by previous CI buils step
    mavenLocal()
}

tasks.test {
    useJUnitPlatform()
}

val coroutinesVersion = property("coroutines_version")
val junit5Version = property("junit5_version")

kotlin {
    jvmToolchain(8)
    dependencies {
        implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:$coroutinesVersion")
        testImplementation("org.junit.jupiter:junit-jupiter-engine:$junit5Version")
    }
}
