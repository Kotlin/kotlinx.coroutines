import org.gradle.api.*
import org.gradle.api.artifacts.dsl.*
import org.gradle.api.artifacts.repositories.*
import org.gradle.api.initialization.dsl.*
import org.gradle.kotlin.dsl.*
import org.jetbrains.kotlin.gradle.targets.js.nodejs.*
import org.jetbrains.kotlin.gradle.targets.js.yarn.*
import java.net.*

/**
 * Enabled via environment variable, so that it can be reliably accessed from any piece of the build script,
 * including buildSrc within TeamCity CI.
 */
private val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true

/**
 *  The list of repositories supported by cache redirector should be synced with the list at https://cache-redirector.jetbrains.com/redirects_generated.html
 *  To add a repository to the list create an issue in ADM project (example issue https://youtrack.jetbrains.com/issue/IJI-149)
 */
private val mirroredUrls = listOf(
    "https://cdn.azul.com/zulu/bin",
    "https://clojars.org/repo",
    "https://dl.google.com/android/repository",
    "https://dl.google.com/dl/android/maven2",
    "https://dl.google.com/dl/android/studio/ide-zips",
    "https://dl.google.com/go",
    "https://download.jetbrains.com",
    "https://github.com/yarnpkg/yarn/releases/download",
    "https://jitpack.io",
    "https://maven.pkg.jetbrains.space/kotlin/p/kotlin/bootstrap",
    "https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev",
    "https://maven.pkg.jetbrains.space/kotlin/p/kotlin/eap",
    "https://nodejs.org/dist",
    "https://oss.sonatype.org/content/repositories/releases",
    "https://oss.sonatype.org/content/repositories/snapshots",
    "https://oss.sonatype.org/content/repositories/staging",
    "https://packages.confluent.io/maven/",
    "https://plugins.gradle.org/m2",
    "https://plugins.jetbrains.com/maven",
    "https://repo.grails.org/grails/core",
    "https://repo.jenkins-ci.org/releases",
    "https://repo.maven.apache.org/maven2",
    "https://repo.spring.io/milestone",
    "https://repo.typesafe.com/typesafe/ivy-releases",
    "https://repo1.maven.org/maven2",
    "https://services.gradle.org",
    "https://www.exasol.com/artifactory/exasol-releases",
    "https://www.jetbrains.com/intellij-repository/nightly",
    "https://www.jetbrains.com/intellij-repository/releases",
    "https://www.jetbrains.com/intellij-repository/snapshots",
    "https://www.myget.org/F/intellij-go-snapshots/maven",
    "https://www.myget.org/F/rd-model-snapshots/maven",
    "https://www.myget.org/F/rd-snapshots/maven",
    "https://www.python.org/ftp",
)

private val aliases = mapOf(
    "https://repo.maven.apache.org/maven2" to "https://repo1.maven.org/maven2" // Maven Central
)

private fun URI.toCacheRedirectorUri() = URI("https://cache-redirector.jetbrains.com/$host/$path")

private fun URI.maybeRedirect(): URI? {
    val url = toString().trimEnd('/')
    val dealiasedUrl = aliases.getOrDefault(url, url)

    return if (mirroredUrls.any { dealiasedUrl.startsWith(it) }) {
        URI(dealiasedUrl).toCacheRedirectorUri()
    } else {
        null
    }
}

private fun URI.isCachedOrLocal() = scheme == "file" ||
    host == "cache-redirector.jetbrains.com" ||
    host == "teamcity.jetbrains.com" ||
    host == "buildserver.labs.intellij.net"

private fun Project.checkRedirectUrl(url: URI, containerName: String): URI {
    val redirected = url.maybeRedirect()
    if (redirected == null && !url.isCachedOrLocal()) {
        val msg = "Repository $url in $containerName should be cached with cache-redirector"
        val details = "Using non cached repository may lead to download failures in CI builds." +
            " Check buildSrc/src/main/kotlin/CacheRedirector.kt for details."
        logger.warn("WARNING - $msg\n$details")
    }
    return if (cacheRedirectorEnabled) redirected ?: url else url
}

private fun Project.checkRedirect(repositories: RepositoryHandler, containerName: String) {
    if (cacheRedirectorEnabled) {
        logger.info("Redirecting repositories for $containerName")
    }
    for (repository in repositories) {
        when (repository) {
            is MavenArtifactRepository -> repository.url = checkRedirectUrl(repository.url, containerName)
            is IvyArtifactRepository -> repository.url = checkRedirectUrl(repository.url, containerName)
        }
    }
}

@Suppress("DEPRECATION", "DEPRECATION_ERROR") // KT-68597, KT-68597
private fun Project.configureYarnAndNodeRedirects() {
    if (CacheRedirector.isEnabled) {
        val yarnRootExtension = extensions.findByType<YarnRootExtension>()
        yarnRootExtension?.downloadBaseUrl?.let {
            yarnRootExtension.downloadBaseUrl = CacheRedirector.maybeRedirect(it)
        }

        val nodeJsExtension = rootProject.extensions.findByType<NodeJsRootExtension>()
        nodeJsExtension?.downloadBaseUrl?.let {
            nodeJsExtension.downloadBaseUrl = CacheRedirector.maybeRedirect(it)
        }
    }
}

// Used from Groovy scripts
// TODO get rid of Groovy, come up with a proper convention for rootProject vs arbitrary project argument
object CacheRedirector {
    /**
     * Substitutes repositories in buildScript { } block.
     */
    @JvmStatic
    fun ScriptHandler.configureBuildScript(rootProject: Project) {
        rootProject.checkRedirect(repositories, "${rootProject.displayName} buildscript")
    }

    @JvmStatic
    fun configure(project: Project) {
        project.checkRedirect(project.repositories, project.displayName)
    }

    /**
     * Configures JS-specific extensions to use
     */
    @JvmStatic
    fun configureJsPackageManagers(project: Project) {
        project.configureYarnAndNodeRedirects()
    }

    @JvmStatic
    fun maybeRedirect(url: String): String {
        if (!cacheRedirectorEnabled) return url
        return URI(url).maybeRedirect()?.toString() ?: url
    }

    @JvmStatic
    val isEnabled get() = cacheRedirectorEnabled
}
