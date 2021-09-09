/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.tasks.InputFile
import org.gradle.api.tasks.InputFiles
import org.gradle.api.tasks.JavaExec
import org.gradle.api.tasks.OutputDirectory
import org.gradle.api.tasks.bundling.Zip
import org.gradle.kotlin.dsl.get
import org.gradle.kotlin.dsl.named
import java.io.File

/*
 * Task used by our ui/android tests to test minification results
 * and keep track of size of the binary.
 * TODO move back to kotlinx-coroutines-android when it's migrated to the kts
 */
open class RunR8 : JavaExec() {

    @OutputDirectory
    lateinit var outputDex: File

    @InputFile
    lateinit var inputConfig: File

    @InputFile
    val inputConfigCommon: File = File("testdata/r8-test-common.pro")

    @InputFiles
    val jarFile: File = project.tasks.named<Zip>("jar").get().archivePath

    init {
        classpath = project.configurations["r8"]
        main = "com.android.tools.r8.R8"
    }

    override fun exec() {
        // Resolve classpath only during execution
        val arguments = mutableListOf(
            "--release",
            "--no-desugaring",
            "--output", outputDex.absolutePath,
            "--pg-conf", inputConfig.absolutePath
        )
        arguments.addAll(project.configurations["runtimeClasspath"].files.map { it.absolutePath })
        arguments.add(jarFile.absolutePath)

        args = arguments

        project.delete(outputDex)
        outputDex.mkdirs()

        super.exec()
    }
}
