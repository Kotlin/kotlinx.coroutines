package kotlinx.coroutines.debug.transformer

import kotlinx.coroutines.debug.manager.*
import org.jetbrains.org.objectweb.asm.ClassReader
import org.jetbrains.org.objectweb.asm.ClassWriter
import org.jetbrains.org.objectweb.asm.Opcodes
import org.jetbrains.org.objectweb.asm.Type
import org.jetbrains.org.objectweb.asm.tree.ClassNode
import org.jetbrains.org.objectweb.asm.tree.MethodInsnNode
import org.jetbrains.org.objectweb.asm.tree.MethodNode
import org.jetbrains.org.objectweb.asm.tree.VarInsnNode
import java.io.File
import java.lang.instrument.ClassFileTransformer
import java.security.ProtectionDomain


private fun ClassNode.isCoroutineImplOrSubType() =
        name == COROUTINE_IMPL_TYPE.internalName || superName == COROUTINE_IMPL_TYPE.internalName

private fun argumentVarIndex(argumentTypes: Array<Type>, argumentIndex: Int) =
        argumentTypes.take(argumentIndex).map { it.size }.sum()

private fun MethodNode.findContinuationVarIndex(classNode: ClassNode): Int {
    // after kotlin 1.1.4-3 continuation for named function isn't stored into the same slot where continuation parameter
    // of function is located, so we should look at slot from where state machine extract its index
    if (classNode.isCoroutineImplOrSubType()) return 0 //index of `this`
    require(isSuspend(), { "Method should be suspend, got $desc instead" })
    val fsm = instructions.sequence.firstOrNull { it.isStateMachineStartsHere() }
    if (fsm != null) {
        val loadContinuationInsn = fsm.nextMeaningful?.nextMeaningful
        return requireNotNull(loadContinuationInsn as VarInsnNode,
                { "loadContinuationInsn should be VarInsnNode" }).`var`
    }
    // fallback strategy (i have no idea how to handle this)
    val continuationArgIndex = Type.getType(desc).argumentTypes.size - continuationOffsetFromEndInDesc(name)
    val isStatic = access and Opcodes.ACC_STATIC != 0
    return argumentVarIndex(Type.getArgumentTypes(desc), continuationArgIndex) + if (isStatic) 0 else 1
}

private fun MethodNode.addSuspendCallHandlers(
        suspendCallsInThisMethod: List<MethodInsnNode>,
        continuationVarIndex: Int,
        classNode: ClassNode
) {
    val lines = instructions.methodCallLineNumber()
    suspendCallsInThisMethod.forEach {
        val position = CallPosition(classNode.sourceFile, lines[it] ?: -1)
        val call = SuspendCall(it.buildMethodId(), this.buildMethodId(classNode), position)
        val key = allSuspendCallsMap.classNameIndexedPut(classNode.name, call)
        instructions.insert(it, generateAfterSuspendCall(continuationVarIndex, key))
    }
}

private fun MethodNode.transformCreate() {
    val completion = Type.getType(desc).argumentTypes.lastIndex + 1
    debug { "create type: $desc, completion: $completion" }
    var newInsn = instructions.first
    while (newInsn.opcode != Opcodes.NEW)
        newInsn = newInsn?.nextMeaningful
    instructions.insertBefore(newInsn, generateNewWrappedCompletion(completion))
}

private fun MethodNode.transformMethod(classNode: ClassNode) {
    if (isCreateCoroutine(classNode)) {
        transformCreate()
        return
    }
    if (!isSuspend() && !isDoResume) return
    val continuation = findContinuationVarIndex(classNode)
    val isAnonymous = isStateMachineForAnonymousSuspendFunction()
    debug {
        ">>in method ${classNode.name}.${name} with description: ${desc}, " +
                "cont: $continuation, isAnonymous: $isAnonymous"
    }
    if (isDoResume) {
        val key = knownDoResumeFunctionsMap.classNameIndexedPut(classNode.name, buildMethodId(classNode))
        instructions.insert(generateHandleDoResumeCallEnter(continuation, key))
        if (!isAnonymous) return
    }
    val suspendCalls = suspendCallInstructions(classNode)
    if (suspendCalls.isEmpty()) return
    debug {
        buildString { append("suspend calls:\n"); suspendCalls.forEach { append("${it.buildMethodId()}\n") } }
    }
    addSuspendCallHandlers(suspendCalls, continuation, classNode)
}

private fun MethodNode.isTransformed() = instructions.sequence.any { it is MethodInsnNode && it.isEventHandlerCall }

private fun ClassNode.isTransformed() = methods.any { it.isTransformed() }

class CoroutinesDebugTransformer : ClassFileTransformer {
    override fun transform(
            loader: ClassLoader?,
            className: String?,
            classBeingRedefined: Class<*>?,
            protectionDomain: ProtectionDomain?,
            classfileBuffer: ByteArray
    ): ByteArray {
        //if (className?.startsWith(DEBUG_AGENT_PACKAGE_PREFIX) == true && classfileBuffer != null) return classfileBuffer
        val reader = ClassReader(classfileBuffer)
        val classNode = ClassNode()
        reader.accept(classNode, 0)
        if (classNode.isTransformed()) {
            info { "${classNode.name} is already transformed" }
            return classfileBuffer
        }
        for (method in classNode.methods.map { it as MethodNode }) {
            try {
                method.transformMethod(classNode)
            } catch (e: Throwable) {
                exceptions?.appendWithIndex(e)
                val message = "while instrumenting ${classNode.name}.${method.name} with desc: ${method.desc} " +
                        "exception : ${e.stackTraceToString()}"
                error { message }
                debug { message + "\nbytecode: ${classNode.byteCodeString()}" }
            }
        }
        val writer = ClassWriter(ClassWriter.COMPUTE_MAXS)
        classNode.accept(writer)
        return writer.toByteArray()
    }

    fun transformBytes(bytes: ByteArray) = transform(null, null, null, null, bytes)
}

class FilesTransformer(private val inputDir: File, private val outputDir: File = inputDir, logLevel: String = "error") {

    init {
        Logger.config = LoggerConfig(try {
            LogLevel.valueOf(logLevel.toUpperCase())
        } catch (e: IllegalArgumentException) {
            LogLevel.INFO
        })
    }

    fun transform() {
        allSuspendCallsMap.clear()
        knownDoResumeFunctionsMap.clear()
        exceptions = AppendOnlyThreadSafeList()
        outputDir.mkdirs()
        info { "Transforming from $inputDir to $outputDir" }
        inputDir.walk().filter { it.isFile }.forEach { file ->
            if (file.isClassFile()) info { "Transforming $file" }
            val bytes = file.readBytes()
            val outBytes = if (file.isClassFile()) classesTransformer.transformBytes(bytes) else bytes
            if (file.isClassFile() && outBytes.contentEquals(bytes)) info { "nothing changed" }
            val outFile = file.toOutputFile()
            outFile.parentFile.mkdirs()
            outFile.writeBytes(outBytes)
        }
        if (exceptions?.isNotEmpty() == true)
            throw Exception("Encountered errors while transforming", exceptions?.firstOrNull())
        info { "Saving indexes into $outputDir" }
        //if we have many input directories we should append index, not rewrite from scratch
        File(outputDir, ALL_SUSPEND_CALLS_DUMP_FILE_NAME)
                .appendAll(SuspendCall.Companion, allSuspendCallsMap.toList())
        File(outputDir, KNOWND_DORESUME_FUNCTIONS_DUMP_FILE_NAME)
                .appendAll(MethodId.Companion, knownDoResumeFunctionsMap.toList())
    }

    private fun File.toOutputFile() = File(outputDir, relativeTo(inputDir).toString())
}

private val classesTransformer = CoroutinesDebugTransformer()

private fun File.isClassFile() = toString().endsWith(".class")


fun main(args: Array<String>) {
    if (args.size != 1 && args.size != 2) {
        println("Usage: CoroutineDebugTransformerKt <inputDir> (<outputDir>)")
        println("Usage: CoroutineDebugTransformerKt <inputDir;inputDir2> <outputDir>")
        return
    }
    Logger.config = LoggerConfig(LogLevel.ERROR)
    val outputDir = File(args[1])
    val dirs = args[0].split(";").map(::File)

    if (dirs.size > 1 && args.size == 1) {
        println("Usage: CoroutineDebugTransformerKt <inputDir;inputDir2> <outputDir>")
        return
    }

    if (dirs.size == 1) {
        val t = if (args.size == 1) FilesTransformer(dirs.single()) else FilesTransformer(dirs.single(), outputDir)
        t.transform()
    } else {
        dirs.forEach {
            FilesTransformer(it, outputDir).transform()
        }
    }
}