import org.gradle.api.artifacts.transform.InputArtifact
import org.gradle.api.artifacts.transform.TransformAction
import org.gradle.api.artifacts.transform.TransformOutputs
import org.gradle.api.artifacts.transform.TransformParameters
import org.gradle.api.file.FileSystemLocation
import org.gradle.api.provider.Provider
import java.io.File
import java.nio.file.Files
import java.util.zip.ZipEntry
import java.util.zip.ZipFile

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
