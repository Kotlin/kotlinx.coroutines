package kotlinx.coroutines.debug.plugin.gradle

import kotlinx.coroutines.debug.manager.PROPERTY_DEBUG_LOG_LEVEL
import kotlinx.coroutines.debug.manager.PROPERTY_ENABLE_DEBUG
import kotlinx.coroutines.debug.transformer.FilesTransformer
import org.gradle.api.DefaultTask
import org.gradle.api.Plugin
import org.gradle.api.Project
import org.gradle.api.artifacts.Configuration
import org.gradle.api.artifacts.DependencySet
import org.gradle.api.artifacts.ProjectDependency
import org.gradle.api.artifacts.type.ArtifactTypeDefinition
import org.gradle.api.file.FileCollection
import org.gradle.api.internal.artifacts.ArtifactAttributes
import org.gradle.api.internal.artifacts.publish.ArchivePublishArtifact
import org.gradle.api.plugins.JavaPlugin
import org.gradle.api.plugins.JavaPluginConvention
import org.gradle.api.tasks.*
import org.gradle.api.tasks.testing.Test
import org.gradle.jvm.tasks.Jar
import java.io.File

val DEBUGGABLE_CONFIGURATION_NAME = "debuggable"

val TEST_DEBUGGABLE_CONFIGURATION_NAME = "testDebuggable"

val TRANSFORM_MAIN_TASK_NAME = "debuggerTransformMain"

val TRANSFORM_TEST_TASK_NAME = "debuggerTransformTest"

val TEST_WITH_DEBUGGER_TASK_NAME = "testWithDebugger"

val GENERATE_DEBUGGABLE_JAR_TASK_NAME = "generateDebuggableJar"

open class DebuggerTransformerGradlePlugin : Plugin<Project> {

    override fun apply(project: Project) {
        project.pluginManager.apply(JavaPlugin::class.java)

        configureConfiguration(project)
        configureTasks(project)
        configureDebuggableArchive(project)
    }

    private fun configureConfiguration(project: Project) {
        with(project.configurations) {
            getByName(JavaPlugin.RUNTIME_ELEMENTS_CONFIGURATION_NAME)
                    .createDebuggableConfiguration(project, DEBUGGABLE_CONFIGURATION_NAME)
            getByName(JavaPlugin.TEST_RUNTIME_CLASSPATH_CONFIGURATION_NAME)
                    .createDebuggableConfiguration(project, TEST_DEBUGGABLE_CONFIGURATION_NAME)
        }
    }

    private fun Configuration.createDebuggableConfiguration(project: Project, configurationName: String) {
        val createdConfiguration = project.configurations.create(configurationName)
        createdConfiguration.isTransitive = true
        createdConfiguration.defaultDependencies { empty ->
            empty += allDependencies.buildDebuggableDependencies(project)
        }
    }

    private fun ProjectDependency.hasDebuggableConfiguration() =
            dependencyProject.configurations.asSequence().any { it.name == DEBUGGABLE_CONFIGURATION_NAME }

    private fun DependencySet.buildDebuggableDependencies(project: Project) =
            map {
                if (it is ProjectDependency && it.hasDebuggableConfiguration()) {
                    val childConfiguration = it.dependencyProject.configurations.getByName(DEBUGGABLE_CONFIGURATION_NAME)
                    childConfiguration.resolve()
                    project.dependencies.project(
                            mapOf("path" to it.dependencyProject.path, "configuration" to DEBUGGABLE_CONFIGURATION_NAME)
                    )
                } else it
            }

    private fun configureTasks(project: Project) {
        project.tasks.create(TRANSFORM_MAIN_TASK_NAME, DebuggerTransformMainTask::class.java)
        project.tasks.create(TRANSFORM_TEST_TASK_NAME, DebuggerTransformTestTask::class.java)
        project.tasks.create(TEST_WITH_DEBUGGER_TASK_NAME, TestWithDebuggerTask::class.java)
    }

    private fun configureDebuggableArchive(project: Project) {
        val debuggableJar = project.tasks.create(GENERATE_DEBUGGABLE_JAR_TASK_NAME, Jar::class.java).apply {
            description = "Assembles a jar archive containing the main classes transformed by debugger transformer."
            classifier = "debuggable"
            from(project.tasks.getByName(TRANSFORM_MAIN_TASK_NAME).outputs.files,
                    project.sourceSets().findByName(SourceSet.MAIN_SOURCE_SET_NAME)!!.resources)
        }
        with(project.configurations.getByName(DEBUGGABLE_CONFIGURATION_NAME).outgoing) {
            artifacts += ArchivePublishArtifact(debuggableJar)
            attributes.attribute(ArtifactAttributes.ARTIFACT_FORMAT, ArtifactTypeDefinition.JAR_TYPE)
        }
    }
}

open class TestWithDebuggerTask : Test() {
    private val DEFAULT_LOG_LEVEL = "error"

    init {
        classpath = project.configurations.getByName(DEBUGGABLE_CONFIGURATION_NAME) +
                project.tasks.getByName(TRANSFORM_MAIN_TASK_NAME).outputs.files +
                project.sourceSets().findByName(SourceSet.MAIN_SOURCE_SET_NAME)!!.resources +
                project.configurations.getByName(TEST_DEBUGGABLE_CONFIGURATION_NAME) +
                project.tasks.getByName(TRANSFORM_TEST_TASK_NAME).outputs.files +
                project.sourceSets().findByName(SourceSet.TEST_SOURCE_SET_NAME)!!.resources

        testClassesDirs = project.tasks.getByName(TRANSFORM_TEST_TASK_NAME).outputs.files

        systemProperty(PROPERTY_ENABLE_DEBUG, true)
        systemProperty(PROPERTY_DEBUG_LOG_LEVEL, DEFAULT_LOG_LEVEL)
    }

    @Input
    open var logLevel: String = DEFAULT_LOG_LEVEL
        set(value) {
            field = value
            systemProperty(PROPERTY_DEBUG_LOG_LEVEL, value)
        }
}

open class DebuggerTransformTask : DefaultTask() {

    @InputFiles
    open lateinit var inputFiles: FileCollection
    @OutputDirectory
    open lateinit var outputDir: File
    @Input
    open var logLevel: String = "error"

    @TaskAction
    fun transform() {
        outputDir.deleteRecursively()
        inputFiles.forEach {
            FilesTransformer(it, outputDir, logLevel).transform()
        }
    }
}

private fun Project.sourceSets() = convention.getPlugin(JavaPluginConvention::class.java).sourceSets //FIXME?

open class PreDefinedGenericDebuggerTransformTask(inputSourceSetName: String) : DebuggerTransformTask() {

    private val CLASSES_DEBUGGABLE = "classes-debuggable"

    @InputFiles
    override var inputFiles: FileCollection = project.sourceSets().findByName(inputSourceSetName)!!.output.classesDirs
    @OutputDirectory
    override var outputDir = File(File(project.buildDir, CLASSES_DEBUGGABLE), inputSourceSetName)
    @Input
    override var logLevel = "error"
}

open class DebuggerTransformMainTask : PreDefinedGenericDebuggerTransformTask(SourceSet.MAIN_SOURCE_SET_NAME)

open class DebuggerTransformTestTask : PreDefinedGenericDebuggerTransformTask(SourceSet.TEST_SOURCE_SET_NAME)
