import org.gradle.api.publish.maven.internal.publication.DefaultMavenPublication
import org.gradle.api.publish.tasks.GenerateModuleMetadata
import java.util.Locale

plugins {
    id("java-platform")
}

val name = project.name

dependencies {
    constraints {
        rootProject.subprojects.forEach {
            if (unpublished.contains(it.name)) return@forEach
            if (it.name == name) return@forEach
            if (!it.plugins.hasPlugin("maven-publish")) return@forEach
            evaluationDependsOn(it.path)
            it.publishing.publications.all {
                this as MavenPublication
                this@constraints.api(mapOf("group" to groupId, "name" to artifactId, "version" to version))
            }
        }
    }
}

publishing {
    publications {
        create<MavenPublication>("mavenBom") {
            from(components["javaPlatform"])
        }
        // Disable metadata publication
        forEach { pub ->
            pub as DefaultMavenPublication
            pub.unsetModuleDescriptorGenerator()
            tasks.matching {
                it.name == "generateMetadataFileFor${ pub.name.replaceFirstChar { it.uppercaseChar() } }Publication"
            }.all {
                onlyIf { false }
            }
        }
    }
}

fun DefaultMavenPublication.unsetModuleDescriptorGenerator() {
    @Suppress("NULL_FOR_NONNULL_TYPE")
    val generator: TaskProvider<GenerateModuleMetadata> = null
    setModuleDescriptorGenerator(generator)
}
