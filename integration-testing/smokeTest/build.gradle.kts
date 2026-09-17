import org.jetbrains.kotlin.gradle.dsl.JvmTarget

plugins {
    id("org.jetbrains.kotlin.jvm")
}

val coroutinesVersion = providers.gradleProperty("coroutines_version").get()

kotlin {
    jvmToolchain(17)
    compilerOptions.jvmTarget = JvmTarget.JVM_1_8
    sourceSets {
        main { kotlin.srcDir("src/commonMain/kotlin") }
        test { kotlin.srcDir("src/commonTest/kotlin") }
    }
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

dependencies {
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
    testImplementation("org.jetbrains.kotlinx:kotlinx-coroutines-test:$coroutinesVersion")
    testImplementation(kotlin("test-junit"))
}
