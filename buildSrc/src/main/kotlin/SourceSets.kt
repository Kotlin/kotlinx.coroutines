import org.gradle.api.*
import org.jetbrains.kotlin.gradle.plugin.*
import org.gradle.kotlin.dsl.*

fun KotlinSourceSet.configureDirectoryPaths() {
    if (project.isMultiplatform) {
        val srcDir = if (name.endsWith("Main")) "src" else "test"
        val platform = name.dropLast(4)
        kotlin.srcDir("$platform/$srcDir")
        if (name == "jvmMain") {
            resources.srcDir("$platform/resources")
        } else if (name == "jvmTest") {
            resources.srcDir("$platform/test-resources")
        }
    } else if (platformOf(project) == "jvm") {
        when (name) {
            "main" -> {
                kotlin.srcDir("src")
                resources.srcDir("resources")
            }
            "test" -> {
                kotlin.srcDir("test")
                resources.srcDir("test-resources")
            }
        }
    } else {
        throw IllegalArgumentException("Unclear how to configure source sets for ${project.name}")
    }
}

/**
 * Creates shared source sets for a group of source sets.
 *
 * [reverseDependencies] is a list of prefixes of names of source sets that depend on the new source set.
 * [dependencies] is a list of prefixes of names of source sets that the new source set depends on.
 * [groupName] is the prefix of the names of the new source sets.
 *
 * The suffixes of the source sets are "Main" and "Test".
 */
fun NamedDomainObjectContainer<KotlinSourceSet>.groupSourceSets(
    groupName: String,
    reverseDependencies: List<String>,
    dependencies: List<String>
) {
    val sourceSetSuffixes = listOf("Main", "Test")
    for (suffix in sourceSetSuffixes) {
        register(groupName + suffix) {
            for (dep in dependencies) {
                dependsOn(get(dep + suffix))
            }
            for (revDep in reverseDependencies) {
                get(revDep + suffix).dependsOn(this)
            }
        }
    }
}
