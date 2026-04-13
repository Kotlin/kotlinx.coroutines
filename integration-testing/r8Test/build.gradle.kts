plugins {
    kotlin("jvm")
}

val coroutinesVersion = property("coroutines_version").toString()

configurations {
    create("r8")
}

dependencies {
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
    "r8"("com.android.tools.build:builder:8.1.0")
}

// The R8 logic below was taken from `ui/kotlinx-coroutines-android/build.gradle.kts`

val r8OutputDir = layout.buildDirectory.dir("r8out")

val runR8 by tasks.registering(RunR8::class) {
    outputDir = r8OutputDir.get().asFile
    inputConfig = file("r8-rules.pro")

    dependsOn("jar")
}

tasks.register("testGcAnchor") {
    dependsOn(runR8)

    doLast {
        project.javaexec {
            mainClass.set("GcAnchorKt")
            classpath = files(r8OutputDir)
        }
    }
}

open class RunR8 : JavaExec() {

    @OutputDirectory
    lateinit var outputDir: File

    @InputFile
    lateinit var inputConfig: File

    @InputFiles
    val jarFile: File = project.tasks.named<Zip>("jar").get().archiveFile.get().asFile

    init {
        classpath = project.configurations["r8"]
        mainClass = "com.android.tools.r8.R8"
    }

    override fun exec() {
        val arguments = mutableListOf(
            "--classfile",
            "--release",
            "--no-minification", // avoid class name collisions on case-insensitive filesystems
            "--pg-conf", inputConfig.absolutePath,
            "--lib", System.getProperty("java.home"),
            "--output", outputDir.absolutePath,
        )
        arguments.addAll(project.configurations["runtimeClasspath"].files.map { it.absolutePath })
        arguments.add(jarFile.absolutePath)

        args = arguments

        project.delete(outputDir)
        outputDir.mkdirs()

        super.exec()
    }
}
