configurations {
    create("r8")
}

repositories {
    mavenCentral()
}

project.configureAar()

dependencies {
    configureAarUnpacking()

    compileOnly("com.google.android:android:${version("android")}")
    compileOnly("androidx.annotation:annotation:${version("androidx_annotation")}")

    testImplementation("com.google.android:android:${version("android")}")
    testImplementation("org.robolectric:robolectric:${version("robolectric")}")
    // Required by robolectric
    testImplementation("androidx.test:core:1.2.0")
    testImplementation("androidx.test:monitor:1.2.0")


    testImplementation("org.smali:baksmali:${version("baksmali")}")
    "r8"("com.android.tools.build:builder:8.1.0")
}

val optimizedDexDir = layout.buildDirectory.dir("dex-optim/")
val unOptimizedDexDir = layout.buildDirectory.dir("dex-unoptim/")

val optimizedDexFile = optimizedDexDir.map { it.dir("classes.dex") } .get().asFile
val unOptimizedDexFile = unOptimizedDexDir.map { it.dir("classes.dex") }.get().asFile

val runR8 by tasks.registering(RunR8::class) {
    outputDex = optimizedDexDir.get().asFile
    inputConfig = file("testdata/r8-test-rules.pro")

    dependsOn("jar")
}

val runR8NoOptim by tasks.registering(RunR8::class) {
    outputDex = unOptimizedDexDir.get().asFile
    inputConfig = file("testdata/r8-test-rules-no-optim.pro")

    dependsOn("jar")
}

tasks.test {
    // Ensure the R8-processed dex is built and supply its path as a property to the test.
    dependsOn(runR8)
    dependsOn(runR8NoOptim)

    inputs.files(optimizedDexFile, unOptimizedDexFile)

    systemProperty("dexPath", optimizedDexFile.absolutePath)
    systemProperty("noOptimDexPath", unOptimizedDexFile.absolutePath)

    // Output custom metric with the size of the optimized dex
    doLast {
        println("##teamcity[buildStatisticValue key='optimizedDexSize' value='${optimizedDexFile.length()}']")
    }
}

externalDocumentationLink(
    url = "https://developer.android.com/reference/"
)
/*
 * Task used by our ui/android tests to test minification results and keep track of size of the binary.
 */
open class RunR8 : JavaExec() {

    @OutputDirectory
    lateinit var outputDex: File

    @InputFile
    lateinit var inputConfig: File

    @InputFile
    val inputConfigCommon: File = File("testdata/r8-test-common.pro")

    @InputFiles
    val jarFile: File = project.tasks.named<Zip>("jar").get().archiveFile.get().asFile

    init {
        classpath = project.configurations["r8"]
        mainClass = "com.android.tools.r8.R8"
    }

    override fun exec() {
        // Resolve classpath only during execution
        val arguments = mutableListOf(
            "--release",
            "--no-desugaring",
            "--min-api", "26",
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
