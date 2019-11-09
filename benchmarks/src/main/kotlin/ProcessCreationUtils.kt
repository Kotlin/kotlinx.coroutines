private val SEPARATOR = System.getProperty("file.separator")
private val CLASS_PATH = System.getProperty("java.class.path")
private val JAVA_PATH = (System.getProperty("java.home") + "${SEPARATOR}bin${SEPARATOR}java")

fun runProcess(classNameToRun : String, jvmOptions : List<String>, args : Array<String>) : Int {
    val runJavaProcessCommand = ArrayList<String>()
    runJavaProcessCommand.run {
        this.add(JAVA_PATH)
        this.addAll(jvmOptions)
        this.add("-cp")
        this.add(CLASS_PATH)
        this.add(classNameToRun)
        this.addAll(args)
    }

    val processBuilder = ProcessBuilder(runJavaProcessCommand)
    val process = processBuilder.inheritIO().redirectError(ProcessBuilder.Redirect.INHERIT).start()

    return process.waitFor()
}