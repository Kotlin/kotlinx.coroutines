import org.gradle.api.Project

fun Project.version(target: String): String =
    property("${target}_version") as String
