/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.DefaultTask
import org.gradle.api.Plugin
import org.gradle.api.Project
import org.gradle.api.artifacts.Configuration
import org.gradle.api.attributes.Attribute
import org.gradle.api.attributes.Bundling
import org.gradle.api.attributes.Category
import org.gradle.api.attributes.LibraryElements
import org.gradle.api.attributes.Usage
import org.gradle.api.attributes.java.TargetJvmEnvironment
import org.gradle.api.component.AdhocComponentWithVariants
import org.gradle.api.file.*
import org.gradle.api.provider.Property
import org.gradle.api.publish.PublishingExtension
import org.gradle.api.publish.maven.MavenPublication
import org.gradle.api.publish.maven.plugins.MavenPublishPlugin
import org.gradle.api.tasks.*
import org.gradle.jvm.tasks.Jar
import org.gradle.kotlin.dsl.*

class AndroidJarPlugin : Plugin<Project> {
    override fun apply(project: Project) {
        if (!project.pluginManager.hasPlugin("java-library")) {
            error("com.android.android-jar plugin must be applied on a java-library project.")
        }
        with(project) {
            val extension = extensions.create<AndroidJarExtension>("androidJar")

            val manifestTask = tasks.register<AarManifestTask>("aarManifest") {
                manifestFile.set(layout.buildDirectory.file("intermediates/aar/AndroidManifest.xml"))
                minSdk = extension.minSdkVersion ?: error("androidJar.minSdk cannot be null")
                namespace = extension.namespace ?: error("androidJar.namespace cannot be null")
            }

            val aarTask = tasks.register<Jar>("aar") {
                val jarTask = tasks.named<Jar>("jar")
                archiveFileName.set(jarTask.flatMap {
                    it.archiveFileName.map { fileName -> fileName.replace(".jar", ".aar") }
                })
                archiveExtension.set("aar")
                from(
                    jarTask.flatMap { it.archiveFile },
                    manifestTask.flatMap { it.manifestFile }
                )
                from(*extension.additionalFiles.toTypedArray())
                rename { fileName ->
                    if (fileName.endsWith(".jar")) {
                        "classes.jar"
                    } else {
                        fileName
                    }
                }
                duplicatesStrategy = DuplicatesStrategy.FAIL
            }

            val runtimeConfiguration = configurations.create("aarRuntime") {
                extendsFrom(
                    configurations.getByName("implementation"),
                    configurations.getByName("runtimeOnly")
                )
                applyCommonAttributes(this)
                attributes {
                    attribute(
                        Usage.USAGE_ATTRIBUTE,
                        objects.named(Usage::class.java, Usage.JAVA_RUNTIME)
                    )
                }
            }

            val apiConfiguration = configurations.create("aarApi") {
                extendsFrom(
                    configurations.getByName("api")
                )
                applyCommonAttributes(this)
                attributes {
                    attribute(
                        Usage.USAGE_ATTRIBUTE,
                        objects.named(Usage::class.java, Usage.JAVA_API)
                    )
                }
            }

            artifacts {
                add(runtimeConfiguration.name, aarTask)
                add(apiConfiguration.name, aarTask)
            }

            components.getByName("java") {
                (this as AdhocComponentWithVariants).apply {
                    addVariantsFromConfiguration(runtimeConfiguration) {
                        mapToOptional()
                    }
                    addVariantsFromConfiguration(apiConfiguration) {
                        mapToOptional()
                    }
                }
            }
            extensions.configure<PublishingExtension> {
                publications.withType<MavenPublication>().all {
                    pom {
                        packaging = "jar"
                    }
                }
            }
        }
    }

    private fun Project.applyCommonAttributes(configuration: Configuration) {
        configuration.attributes {
            attribute(
                Category.CATEGORY_ATTRIBUTE,
                objects.named(Category::class.java, Category.LIBRARY)
            )
            attribute(
                Bundling.BUNDLING_ATTRIBUTE,
                objects.named(Bundling::class.java, Bundling.EXTERNAL)
            )
            attribute(
                LibraryElements.LIBRARY_ELEMENTS_ATTRIBUTE,
                objects.named(LibraryElements::class.java, "aar")
            )
            attribute(
                TargetJvmEnvironment.TARGET_JVM_ENVIRONMENT_ATTRIBUTE,
                objects.named(
                    TargetJvmEnvironment::class.java,
                    TargetJvmEnvironment.ANDROID
                )
            )
            attribute(
                Attribute.of("org.jetbrains.kotlin.platform.type", String::class.java),
                "androidJvm"
            )
        }
    }
}

abstract class AndroidJarExtension {
    /**
     * To be used for the AndroidManifest.xml package attribute.
     */
    abstract var namespace: String?

    /**
     * To be used for the AndroidManifest.xml min-sdk.
     */
    abstract var minSdkVersion: Int?

    /**
     * These additional files will be passed to the Jar task and evaluated as per [Project.files].
     */
    val additionalFiles: MutableList<Any> = mutableListOf()
}

abstract class AarManifestTask : DefaultTask() {

    @get:OutputFile
    abstract val manifestFile: RegularFileProperty

    @get:Input
    abstract var minSdk: Int

    @get:Input
    abstract var namespace: String

    @TaskAction
    fun createManifest() {
        val file = manifestFile.get().asFile
        file.parentFile.mkdirs()
        file.writeText("""
            <?xml version="1.0" encoding="utf-8"?>
            <manifest xmlns:android="http://schemas.android.com/apk/res/android"
                package="$namespace" >
            
                <uses-sdk android:minSdkVersion="$minSdk" />
            </manifest>
        """.trimIndent())
    }

}