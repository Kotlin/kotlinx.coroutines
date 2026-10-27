apply(from = "./src/main/kotlin/repositories.settings.gradle.kts")

pluginManagement {
    plugins {
        kotlin("jvm") version("kotlin") apply false
        kotlin("multiplatform") version("kotlin") apply false
        id("org.jetbrains.kotlinx.binary-compatibility-validator") version("bcv") apply false
        id("org.jetbrains.dokka") version("dokka") apply false
        id("org.jetbrains.kotlinx.knit") version("knit") apply false
        id("ru.vyarus.gradle-animalsniffer-plugin") version("animalsniffer") apply false
        id("org.jetbrains.kotlinx.atomicfu") version("atomicfu") apply false
        id("org.jetbrains.kotlinx.kover") version("kover") apply false
    }
}
