import org.jetbrains.kotlin.gradle.plugin.*

fun KotlinSourceSet.configureDirectoryPaths() {
    val sourceDir = when (name) {
        "main" -> "src"
        "test" -> "test"
        else -> return
    }
    val resourceDir = if (name == "main") "resources" else "test-resources"
    if (project.hasSharedSources) {
        kotlin.srcDirs("common/$sourceDir", "concurrent/$sourceDir", "jvm/$sourceDir")
        resources.srcDir("jvm/$resourceDir")
    } else {
        kotlin.srcDir(sourceDir)
        resources.srcDir(resourceDir)
    }
}
