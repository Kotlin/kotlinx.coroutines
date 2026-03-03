plugins {
    kotlin("jvm")
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
