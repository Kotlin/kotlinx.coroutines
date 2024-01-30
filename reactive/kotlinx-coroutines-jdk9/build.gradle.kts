import org.jetbrains.kotlin.gradle.dsl.*

dependencies {
    implementation(project(":kotlinx-coroutines-reactive"))
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_9
    targetCompatibility = JavaVersion.VERSION_1_9
}

tasks {
    compileKotlin {
        compilerOptions.jvmTarget = JvmTarget.JVM_9
    }

    compileTestKotlin {
        compilerOptions.jvmTarget = JvmTarget.JVM_9
    }
}

externalDocumentationLink(
    url = "https://docs.oracle.com/javase/9/docs/api/java/util/concurrent/Flow.html"
)
