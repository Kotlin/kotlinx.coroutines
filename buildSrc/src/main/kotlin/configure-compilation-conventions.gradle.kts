import org.jetbrains.kotlin.gradle.tasks.*
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile

configure(subprojects) {
    val project = this
    if (name in sourceless) return@configure
    apply(plugin = "atomicfu-conventions")
    tasks.withType<KotlinCompilationTask<*>>().configureEach {
        val isMainTaskName = name.startsWith("compileKotlin")
        compilerOptions {
            var versionsAreNotOverridden = true
            getOverriddenKotlinLanguageVersion(project)?.let {
                languageVersion = it
                versionsAreNotOverridden = false
            }
            getOverriddenKotlinApiVersion(project)?.let {
                apiVersion = it
                versionsAreNotOverridden = false
            }
            if (isMainTaskName && versionsAreNotOverridden && !unpublished.contains(project.name)) {
                allWarningsAsErrors = false
                freeCompilerArgs.add("-Xexplicit-api=strict")
            }
            /* Coroutines do not interop with Java and these flags provide a significant
             * (i.e. close to double-digit) reduction in both bytecode and optimized dex size */
            if (this@configureEach is KotlinJvmCompile) {
                freeCompilerArgs.addAll(
                    "-Xno-param-assertions",
                    "-Xno-call-assertions",
                    "-Xno-receiver-assertions"
                )
            }
            if (this@configureEach is KotlinNativeCompile) {
                optIn.addAll(
                    "kotlinx.cinterop.ExperimentalForeignApi",
                    "kotlinx.cinterop.UnsafeNumber",
                    "kotlin.experimental.ExperimentalNativeApi",
                )
            }
            freeCompilerArgs.addAll("-progressive", "-Xexpect-actual-classes")
            optIn.addAll(
                "kotlin.experimental.ExperimentalTypeInference",
                "kotlin.ExperimentalMultiplatform",
                // our own opt-ins that we don't want to bother with in our own code:
                "kotlinx.coroutines.DelicateCoroutinesApi",
                "kotlinx.coroutines.ExperimentalCoroutinesApi",
                "kotlinx.coroutines.ObsoleteCoroutinesApi",
                "kotlinx.coroutines.InternalCoroutinesApi",
                "kotlinx.coroutines.FlowPreview"
            )
        }

    }
}
