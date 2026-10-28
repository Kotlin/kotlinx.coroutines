private val LOGGER: java.util.logging.Logger = java.util.logging.Logger.getLogger("Kotlin settings logger")

private val cacheRedirectorEnabled: Boolean = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true

dependencyResolutionManagement {
    repositoriesMode = RepositoriesMode.PREFER_SETTINGS

    fun RepositoryHandler.gradlePortalWithCacheRedirect() {
        if (cacheRedirectorEnabled) {
            maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        } else {
            maven("https://plugins.gradle.org/m2")
        }
    }

    fun RepositoryHandler.mavenCentralWithCacheRedirect() {
        if (cacheRedirectorEnabled) {
            maven("https://cache-redirector.jetbrains.com/maven-central")
        } else {
            mavenCentral()
        }
    }

    fun ProviderFactory.isSnapshotTrainEnabled(): Boolean =
        gradleProperty("idea.snapshots.enable").orNull?.toBoolean() == true

    fun RepositoryHandler.configureJsRepositories() {
        val cacheRedirectorDomainPrefix = if (cacheRedirectorEnabled) "cache-redirector.jetbrains.com/" else ""
        ivy("https://${cacheRedirectorDomainPrefix}nodejs.org/dist/") {
            name = "Node Distributions at $url"
            patternLayout { artifact("v[revision]/[artifact](-v[revision]-[classifier]).[ext]") }
            metadataSources { artifact() }
            content { includeModule("org.nodejs", "node") }
        }
        ivy("https://${cacheRedirectorDomainPrefix}github.com/yarnpkg/yarn/releases/download") {
            name = "Yarn Distributions at $url"
            patternLayout { artifact("v[revision]/[artifact](-v[revision]).[ext]") }
            metadataSources { artifact() }
            content { includeModule("com.yarnpkg", "yarn") }
        }
    }

    val kotlinDevUrl = providers.gradleProperty("kotlin_repo_url").orNull
    val kotlinVersion = providers.gradleProperty("kotlin_version").orNull
    val configureDevRepo = !kotlinDevUrl.isNullOrEmpty() && !kotlinVersion.isNullOrEmpty()

    if (configureDevRepo) {
        LOGGER.info("Configured Kotlin Compiler version $kotlinVersion and repository URL $kotlinDevUrl")
    }

    repositories {
        if (configureDevRepo) {
            exclusiveContent {
                forRepository {
                    maven(kotlinDevUrl)
                }
                filter {
                    includeVersionByRegex("org.jetbrains.kotlin", ".*", kotlinVersion)
                }
            }
        }

        google {
            content {
                includeGroupByRegex("androidx.*")
                includeGroupByRegex("com\\.google\\.android.*")
                includeGroupByRegex("com\\.android.*")
            }
        }

        if (providers.isSnapshotTrainEnabled()) {
            mavenLocal()
        }
        gradlePortalWithCacheRedirect()
        mavenCentralWithCacheRedirect()

        configureJsRepositories()
    }

    pluginManagement {
        repositories {
            if (configureDevRepo) {
                exclusiveContent {
                    forRepository {
                        maven(kotlinDevUrl)
                    }
                    filter {
                        includeVersionByRegex("org.jetbrains.kotlin", ".*", kotlinVersion)
                    }
                }
            }

            if (providers.isSnapshotTrainEnabled()) {
                mavenLocal()
            }
            gradlePortalWithCacheRedirect()
            mavenCentralWithCacheRedirect()
        }
    }
}

