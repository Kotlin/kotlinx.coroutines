internal val javaVersion: String
    get() = System.getProperty("java.version")!!

internal val javaVersionMajor: Int
    get() = javaVersion
        .substringBefore(".")
        .toInt()
