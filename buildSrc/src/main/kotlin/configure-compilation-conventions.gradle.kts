import org.jetbrains.kotlin.gradle.tasks.*

configure(subprojects) {
    val project = this
    if (name in sourceless) return@configure
    apply(plugin = "org.jetbrains.kotlinx.atomicfu")
    tasks.withType<KotlinCompilationTask<*>>().configureEach {
        val isMainTaskName = name.startsWith("compileKotlin")
        compilerOptions {
            getOverriddenKotlinLanguageVersion(project)?.let {
                languageVersion = it
            }
            getOverriddenKotlinApiVersion(project)?.let {
                apiVersion = it
            }
            if (isMainTaskName && !unpublished.contains(project.name)) {
                setWarningsAsErrors(project)
                freeCompilerArgs.addAll(
                    "-Xexplicit-api=strict",
                    "-Xdont-warn-on-error-suppression",
                )
            }
            configureKotlinUserProject()
            /* Coroutines do not interop with Java and these flags provide a significant
             * (i.e. close to double-digit) reduction in both bytecode and optimized dex size */
            if (this@configureEach is KotlinJvmCompile) {
                freeCompilerArgs.addAll(
                    "-Xno-param-assertions",
                    "-Xno-call-assertions",
                    "-Xno-receiver-assertions",
                    "-Xjvm-default=disable",
                )
            }
            if (this@configureEach is KotlinNativeCompile) {
                optIn.addAll(
                    "kotlinx.cinterop.ExperimentalForeignApi",
                    "kotlinx.cinterop.UnsafeNumber",
                    "kotlin.experimental.ExperimentalNativeApi",
                )
            }
            addExtraCompilerFlags(project)
        }

    }
}
