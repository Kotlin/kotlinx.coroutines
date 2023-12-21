import org.jetbrains.kotlin.gradle.dsl.*

plugins {
    // apply plugin to use autocomplete for Kover DSL
    id("org.jetbrains.kotlinx.kover")
}

val reactorVersion = version("reactor")

dependencies {
    api("io.projectreactor:reactor-core:$reactorVersion")
    api(project(":kotlinx-coroutines-reactive"))
}

java {
    targetCompatibility = JavaVersion.VERSION_1_8
    sourceCompatibility = JavaVersion.VERSION_1_8
}

tasks {
    compileKotlin {
        compilerOptions.jvmTarget = JvmTarget.JVM_1_8
    }

    compileTestKotlin {
        compilerOptions.jvmTarget = JvmTarget.JVM_1_8
    }
}

externalDocumentationLink(
    url = "https://projectreactor.io/docs/core/$reactorVersion/api/"
)


koverReport {
    filters {
        excludes {
            classes(
                "kotlinx.coroutines.reactor.FlowKt", // Deprecated
                "kotlinx.coroutines.reactor.ConvertKt\$asFlux$1" // Deprecated
            )
        }
    }
}
