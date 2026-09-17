import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile

// Redefine source sets because we are not using 'kotlin/main/fqn' folder convention
// TODO: port benchmarks to the same scheme
configure(subprojects.filter { !sourceless.contains(it.name) && it.name != "benchmarks" }) {
    kotlinExtension.sourceSets.forEach {
        it.configureDirectoryPaths()
    }
}

// Compile the existing expect/actual declarations together using the JVM compiler.
// This preserves the source layout without applying the multiplatform Gradle plugin.
configure(subprojects.filter { it.hasSharedSources }) {
    tasks.withType<KotlinJvmCompile>().configureEach {
        val sourceDir = when (name) {
            "compileKotlin" -> "src"
            "compileTestKotlin" -> "test"
            else -> return@configureEach
        }
        compilerOptions {
            optIn.addAll("kotlin.ExperimentalMultiplatform", "kotlin.js.ExperimentalJsExport")
            freeCompilerArgs.addAll(
                "-Xmulti-platform",
                "-Xexpect-actual-classes",
                "-Xfragments=common,concurrent,jvm",
                "-Xfragment-refines=concurrent:common,jvm:concurrent",
            )
            for (fragment in listOf("common", "concurrent", "jvm")) {
                val fragmentSources = fileTree("$fragment/$sourceDir") { include("**/*.kt") }
                freeCompilerArgs.addAll(fragmentSources.elements.map { sources ->
                    sources.map { "-Xfragment-sources=$fragment:${it.asFile.absolutePath}" }
                })
            }
        }
    }
}
