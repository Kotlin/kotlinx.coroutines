dependencyResolutionManagement {
    repositoriesMode = RepositoriesMode.PREFER_SETTINGS

    fun RepositoryHandler.mavenCentralWithCacheRedirect() {
        val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true
        if (cacheRedirectorEnabled) {
            maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        } else {
            maven("https://plugins.gradle.org/m2")
        }
    }

    fun RepositoryHandler.gradlePortalWithCacheRedirect() {
        val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true
        if (cacheRedirectorEnabled) {
            maven("https://cache-redirector.jetbrains.com/maven-central")
        } else {
            mavenCentral()
        }
    }

    fun RepositoryHandler.mavenLocal(isSnapshotTrainEnabled: Boolean) {
        mavenLocal {
            // If it's not a snapshot build, enable local repo only for kotlin and atomicfu artifacts
            if (!isSnapshotTrainEnabled) {
                content {
                    includeVersionByRegex(".*", "(kotlin|atomicfu)", ".*-SNAPSHOT")
                }
            }
        }
    }

    fun RepositoryHandler.configureJsRepositories() {
        val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true
        val cacheRedirectorSuffix = if (cacheRedirectorEnabled) "cache-redirector.jetbrains.com/" else ""
        ivy("https://${cacheRedirectorSuffix}nodejs.org/dist/") {
            name = "Node Distributions at $url"
            patternLayout { artifact("v[revision]/[artifact](-v[revision]-[classifier]).[ext]") }
            metadataSources { artifact() }
            content { includeModule("org.nodejs", "node") }
        }
        ivy("https://${cacheRedirectorSuffix}github.com/yarnpkg/yarn/releases/download") {
            name = "Yarn Distributions at $url"
            patternLayout { artifact("v[revision]/[artifact](-v[revision]).[ext]") }
            metadataSources { artifact() }
            content { includeModule("com.yarnpkg", "yarn") }
        }
    }

    val kotlinDevUrl = providers.gradleProperty("kotlin_repo_url").orNull
    val kotlinVersion = providers.gradleProperty("kotlin_version").orNull

    repositories {
        val build_snapshot_train: String? by settings

        if (!kotlinDevUrl.isNullOrEmpty() && !kotlinVersion.isNullOrEmpty()) {
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

        mavenLocal(build_snapshot_train?.toBoolean() == true)
        mavenCentralWithCacheRedirect()

        configureJsRepositories()
    }

    pluginManagement {
        repositories {
            val build_snapshot_train: String? by settings

            if (!kotlinDevUrl.isNullOrEmpty() && !kotlinVersion.isNullOrEmpty()) {
                exclusiveContent {
                    forRepository {
                        maven(kotlinDevUrl)
                    }
                    filter {
                        includeVersionByRegex("org.jetbrains.kotlin", ".*", kotlinVersion)
                    }
                }
            }

            mavenLocal(build_snapshot_train?.toBoolean() == true)
            gradlePortalWithCacheRedirect()
            mavenCentralWithCacheRedirect()
        }
    }
}

