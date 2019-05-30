package kotlinx.coroutines.internal

import java.io.*
import java.net.*
import java.util.*
import java.util.jar.*
import java.util.zip.*

/**
 * A simplified version of [ServiceLoader].
 * FastServiceLoader locates and instantiates all service providers named in configuration
 * files placed in the resource directory <tt>META-INF/services</tt>.
 *
 * The main difference between this class and classic service loader is in skipping
 * verification JARs. A verification requires reading the whole JAR (and it causes problems and ANRs on Android devices)
 * and prevents only trivial checksum issues. See #878.
 *
 * If any error occurs during loading, it fallbacks to [ServiceLoader], mostly to prevent R8 issues.
 */
internal object FastServiceLoader {
    private const val PREFIX: String = "META-INF/services/"

    internal fun <S> load(service: Class<S>, loader: ClassLoader): List<S> {
        return try {
            loadProviders(service, loader)
        } catch (e: Throwable) {
            // Fallback to default service loader
            ServiceLoader.load(service, loader).toList()
        }
    }

    // Visible for tests
    internal fun <S> loadProviders(service: Class<S>, loader: ClassLoader): List<S> {
        val fullServiceName = PREFIX + service.name
        // Filter out situations when both JAR and regular files are in the classpath (e.g. IDEA)
        val urls = loader.getResources(fullServiceName)
        val providers = urls.toList().flatMap { parse(it) }.toSet()
        require(providers.isNotEmpty()) { "No providers were loaded with FastServiceLoader" }
        return providers.map { getProviderInstance(it, loader, service) }
    }

    private fun <S> getProviderInstance(name: String, loader: ClassLoader, service: Class<S>): S {
        val clazz = Class.forName(name, false, loader)
        require(service.isAssignableFrom(clazz)) { "Expected service of class $service, but found $clazz" }
        return service.cast(clazz.getDeclaredConstructor().newInstance())
    }

    private fun parse(url: URL): List<String> {
        val path = url.toString()
        // Fast-path for JARs
        if (path.startsWith("jar")) {
            val pathToJar = path.substringAfter("jar:file:").substringBefore('!')
            val entry = path.substringAfter("!/")
            // mind the verify = false flag!
            (JarFile(pathToJar, false) as Closeable).use { file ->
                BufferedReader(InputStreamReader((file as JarFile).getInputStream(ZipEntry(entry)), "UTF-8")).use { r ->
                    return parseFile(r)
                }
            }
        }
        // Regular path for everything elese
        return BufferedReader(InputStreamReader(url.openStream())).use { reader ->
            parseFile(reader)
        }
    }

    private fun parseFile(r: BufferedReader): List<String> {
        val names = mutableSetOf<String>()
        while (true) {
            val line = r.readLine() ?: break
            val serviceName = line.substringBefore("#").trim()
            require(serviceName.all { it == '.' || Character.isJavaIdentifierPart(it) }) { "Illegal service provider class name: $serviceName" }
            if (serviceName.isNotEmpty()) {
                names.add(serviceName)
            }
        }
        return names.toList()
    }
}
