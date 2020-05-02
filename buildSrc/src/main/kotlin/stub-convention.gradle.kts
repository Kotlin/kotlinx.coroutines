import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

tasks.named<KotlinCompile>("compileKotlin") {
    kotlinOptions {
        freeCompilerArgs += "-Xallow-kotlin-package"
    }
}
