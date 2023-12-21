import org.gradle.api.publish.maven.internal.publication.DefaultMavenPublication

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
                if (artifactId.endsWith("-kotlinMultiplatform")) return@all
                if (artifactId.endsWith("-metadata")) return@all
                // Skip platform artifacts (like *-linuxx64, *-macosx64)
                // It leads to inconsistent bom when publishing from different platforms
                // (e.g. on linux it will include only linuxx64 artifacts and no macosx64)
                // It shouldn't be a problem as usually consumers need to use generic *-native artifact
                // Gradle will choose correct variant by using metadata attributes
                if (artifacts.any { it.extension == "klib" }) return@all
                this@constraints.api(mapOf("group" to groupId, "name" to artifactId, "version" to version))
            }
        }
    }
}

publishing {
    publications {
        val mavenBom by creating(MavenPublication::class) {
            from(components["javaPlatform"])
        }
        // Disable metadata publication
        forEach { pub ->
            pub as DefaultMavenPublication
            pub.unsetModuleDescriptorGenerator()
            tasks.matching { it.name == "generateMetadataFileFor${pub.name.capitalize()}Publication" }.all {
                onlyIf { false }
            }
        }
    }
}

fun DefaultMavenPublication.unsetModuleDescriptorGenerator() {
    @Suppress("NULL_FOR_NONNULL_TYPE")
    val generator: TaskProvider<Task> = null
    setModuleDescriptorGenerator(generator)
}
