import org.gradle.api.publish.maven.internal.publication.DefaultMavenPublication

plugins {
    id("java-platform")
}

// We use the same version for everything and reading each module's (mutable!) group/version is not Gradle-friendly
val bomGroup = project.group.toString()
val bomVersion = project.version.toString()

dependencies {
    constraints {
        rootProject.subprojects.forEach { module ->
            if (module.name in unpublished || module.isBom) return@forEach
            if (module.isMultiplatform) {
                api("$bomGroup:${module.name}-jvm:$bomVersion")
            }
            api("$bomGroup:${module.name}:$bomVersion")
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
    val generator: TaskProvider<Task> = null
    setModuleDescriptorGenerator(generator)
}
