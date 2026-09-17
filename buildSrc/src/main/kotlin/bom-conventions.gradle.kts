import org.gradle.kotlin.dsl.*
import org.jetbrains.kotlin.gradle.dsl.*


configure(subprojects.filter { it.name !in unpublished }) {
    if (name == "kotlinx-coroutines-bom" || name == "kotlinx.coroutines") return@configure
    dependencies {
        "api"(platform(project(":kotlinx-coroutines-bom")))
    }
}
