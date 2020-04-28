val javaVersion: String
    get() = System.getProperty("java.version")!!

val javaVersionMajor: Int
    get() = javaVersion
        .substringBefore(".")
        .toInt()
