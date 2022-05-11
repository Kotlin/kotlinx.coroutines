import org.jetbrains.dokka.gradle.*
import java.net.*

/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Configures generation of JavaDoc & Dokka artifacts
apply<DokkaPlugin>()
//apply<JavaPlugin>()

fun GradleDokkaSourceSetBuilder.makeLinkMapping(projectDir: File) {
    sourceLink {
        val relPath = rootProject.projectDir.toPath().relativize(projectDir.toPath())
        localDirectory.set(projectDir.resolve("src"))
        remoteUrl.set(URL("https://github.com/kotlin/kotlinx.coroutines/tree/master/$relPath/src"))
        remoteLineSuffix.set("#L")
    }
}

val knit_version: String by project
tasks.withType(DokkaTaskPartial::class).configureEach {
    dependencies {
        plugins("org.jetbrains.kotlinx:dokka-pathsaver-plugin:$knit_version")
    }
}

tasks.withType(DokkaTaskPartial::class).configureEach {
    suppressInheritedMembers.set(true)
    dokkaSourceSets.configureEach {
        jdkVersion.set(11)
        includes.from("README.md")
        noStdlibLink.set(true)

        externalDocumentationLink {
            url.set(URL("https://kotlinlang.org/api/latest/jvm/stdlib/"))
            packageListUrl.set(rootProject.projectDir.toPath().resolve("site/stdlib.package.list").toUri().toURL())
        }

        if (!project.isMultiplatform) {
            dependsOn(project.configurations["compileClasspath"])
        }
    }
}

if (project.name == "kotlinx-coroutines-core") {
    // Custom configuration for MPP modules
    tasks.withType(DokkaTaskPartial::class).configureEach {
        dokkaSourceSets {
            val commonMain by getting {
                makeLinkMapping(project.file("common"))
            }

            val nativeMain by getting {
                makeLinkMapping(project.file("native"))
            }

            val jsMain by getting {
                makeLinkMapping(project.file("js"))
            }

            val jvmMain by getting {
                makeLinkMapping(project.file("jvm"))
            }
        }
    }
}
