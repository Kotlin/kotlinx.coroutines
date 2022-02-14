/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.api.artifacts.transform.InputArtifact
import org.gradle.api.artifacts.transform.TransformAction
import org.gradle.api.artifacts.transform.TransformOutputs
import org.gradle.api.artifacts.transform.TransformParameters
import org.gradle.api.attributes.*
import org.gradle.api.file.FileSystemLocation
import org.gradle.api.provider.Provider
import org.gradle.kotlin.dsl.*
import java.io.File
import java.nio.file.Files
import java.util.zip.ZipEntry
import java.util.zip.ZipFile

// Attributes used by aar dependencies
val artifactType = Attribute.of("artifactType", String::class.java)
val unpackedAar = Attribute.of("unpackedAar", Boolean::class.javaObjectType)

fun Project.configureAar() = configurations.configureEach {
    afterEvaluate {
        if (isCanBeResolved && !isCanBeConsumed) {
            attributes.attribute(unpackedAar, true) // request all AARs to be unpacked
        }
    }
}

fun DependencyHandlerScope.configureAarUnpacking() {
    attributesSchema {
        attribute(unpackedAar)
    }

    artifactTypes {
        create("aar") {
            attributes.attribute(unpackedAar, false)
        }
    }

    registerTransform(UnpackAar::class.java) {
        from.attribute(unpackedAar, false).attribute(artifactType, "aar")
        to.attribute(unpackedAar, true).attribute(artifactType, "jar")
    }
}

@Suppress("UnstableApiUsage")
abstract class UnpackAar : TransformAction<TransformParameters.None> {
    @get:InputArtifact
    abstract val inputArtifact: Provider<FileSystemLocation>

    override fun transform(outputs: TransformOutputs) {
        ZipFile(inputArtifact.get().asFile).use { zip ->
            zip.entries().asSequence()
                .filter { !it.isDirectory }
                .filter { it.name.endsWith(".jar") }
                .forEach { zip.unzip(it, outputs.file(it.name)) }
        }
    }
}

private fun ZipFile.unzip(entry: ZipEntry, output: File) {
    getInputStream(entry).use {
        Files.copy(it, output.toPath())
    }
}
