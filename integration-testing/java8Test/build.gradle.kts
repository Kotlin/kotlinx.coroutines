plugins {
    kotlin("jvm")
}

tasks.test {
    useJUnitPlatform()
}

val coroutinesVersion = providers.gradleProperty("coroutines_version").get()
val junit5Version = providers.gradleProperty("junit5_version").get()

kotlin {
    jvmToolchain(8)
    dependencies {
        implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:$coroutinesVersion")
        testImplementation("org.junit.jupiter:junit-jupiter-engine:$junit5Version")
        testRuntimeOnly("org.junit.platform:junit-platform-launcher")
    }
}
