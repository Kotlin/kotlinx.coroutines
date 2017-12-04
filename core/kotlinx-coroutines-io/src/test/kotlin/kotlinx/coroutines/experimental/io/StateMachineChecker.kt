package kotlinx.coroutines.experimental.io

import org.objectweb.asm.*
import java.io.*

class StateMachineChecker {
    private interface Filter {
        fun nonSuspend(className: String, methodName: String): Boolean
        fun suspend(className: String, methodName: String, hasStateMachine: Boolean): Boolean
    }
    private interface Dumper {
        fun dump(className: String, methodName: String, desc: String, suspend: Boolean, hasStateMachine: Boolean, access: Int)
    }

    private enum class ViewModes : Filter {
        ALL { // dump all methods
            override fun nonSuspend(className: String, methodName: String) = true
            override fun suspend(className: String, methodName: String, hasStateMachine: Boolean) = true
        },
        ALL_SUSPEND { // dump all suspend functions
            override fun nonSuspend(className: String, methodName: String) = false
            override fun suspend(className: String, methodName: String, hasStateMachine: Boolean) = true
        },
        ALL_SUSPEND_SM { // dump all suspend functions with state machine
            override fun nonSuspend(className: String, methodName: String) = false
            override fun suspend(className: String, methodName: String, hasStateMachine: Boolean) = hasStateMachine
        },
        ALL_SUSPEND_SM_FILTERED { // all stateful suspend functions that don't end with Suspend suffix
            override fun nonSuspend(className: String, methodName: String) = false
            override fun suspend(className: String, methodName: String, hasStateMachine: Boolean) =
                    hasStateMachine && !methodName.endsWith("Suspend")
        }
    }

    private class DefaultDumper(private val out: Writer) : Dumper {
        override fun dump(className: String, methodName: String, desc: String, suspend: Boolean, hasStateMachine: Boolean, access: Int) {
            out.write("[")
            if (suspend) out.write("s") else out.write(" ")
            if (hasStateMachine) out.write("M") else out.write(" ")
            out.write(",")

            when {
                access and Opcodes.ACC_PRIVATE != 0 -> out.write("pvt")
                access and Opcodes.ACC_PUBLIC != 0 -> out.write("pub")
                access and Opcodes.ACC_PROTECTED != 0 -> out.write("prt")
                else -> out.write("   ")
            }

            out.write("] ")

            out.write(className.substringAfterLast("/"))
            out.write(".")
            out.write(methodName)
            out.write(simplifyDesc(desc))

            if (access and Opcodes.ACC_SYNTHETIC != 0) {
                out.write(" #synthetic")
            }
            if (access and Opcodes.ACC_DEPRECATED != 0) {
                out.write(" #deprecated")
            }
            if (access and Opcodes.ACC_FINAL == 0) {
                out.write(" #open")
            }
            if (access and Opcodes.ACC_BRIDGE != 0) {
                out.write(" #bridge")
            }

            out.write("\n")
            out.flush()
        }

        private fun simplifyDesc(desc: String): String {
            val components = """\[?(L[^;]+;|[ZBCSIFDJV])""".toRegex().findAll(desc).map { it.value }.toList()

            return buildString {
                append("(")
                val last = components.lastIndex
                for (i in 0 until last) {
                    append(simplifyType(components[i]))
                }
                if (last >= 0) {
                    append(")")
                    append(simplifyType(components[last]))
                } else {
                    append(")?")
                }
            }
        }

        private fun simplifyType(type: String): String {
            return if (type.startsWith("[")) "[" + simplifyType(type.removePrefix("["))
            else if (type.startsWith("L")) "L" + type.removePrefix("L").substringAfterLast("/")
            else type
        }
    }

    private var filter: Filter = ViewModes.ALL_SUSPEND_SM_FILTERED
    private var dumper: Dumper = DefaultDumper(System.out.bufferedWriter())

    private fun process(f: File) {
        val reader = f.inputStream().use { ClassReader(it) }
        reader.accept(object: ClassVisitor(Opcodes.ASM5) {
            private var className: String = "?class"

            override fun visit(version: Int, access: Int, name: String?, signature: String?, superName: String?, interfaces: Array<out String>?) {
                className = name ?: "?class"
                super.visit(version, access, name, signature, superName, interfaces)
            }

            override fun visitMethod(access: Int, name: String?, desc: String?, signature: String?, exceptions: Array<out String>?): MethodVisitor? {
                if (desc != null && desc.contains("Lkotlin/coroutines/experimental/Continuation;)")) {
                    val visitor = MyMethodVisitor
                    visitor.filter = filter
                    visitor.dumper = dumper

                    visitor.className = className
                    visitor.methodName = name ?: "?method"
                    visitor.methodDesc = desc
                    visitor.access = access

                    return visitor
                } else if (filter.nonSuspend(className, name ?: "?method")) {
                    if (filter.nonSuspend(className, name ?: "?method")) {
                        dumper.dump(className, name ?: "?method", desc ?: "", false, false, access)
                    }
                }
                return super.visitMethod(access, name, desc, signature, exceptions)
            }
        }, 0)
    }

    private fun processDir(dir: File) {
        dir.walkTopDown().asSequence().filter { it.name.endsWith(".class") && it.isFile }.forEach { file ->
            process(file)
        }
    }

    private object MyMethodVisitor : MethodVisitor(Opcodes.ASM5) {
        lateinit var filter: Filter
        lateinit var dumper: Dumper

        var className: String = "?class"
        var methodName: String = "?method"
        var methodDesc: String = "?desc"
        var access: Int = 0

        var foundGetLabel = false
        var foundTableSwitch = false

        override fun visitMethodInsn(opcode: Int, owner: String?, name: String?, desc: String?, itf: Boolean) {
            if(name == "getLabel") {
                foundGetLabel = true
            }

            super.visitMethodInsn(opcode, owner, name, desc, itf)
        }

        override fun visitTableSwitchInsn(min: Int, max: Int, dflt: Label?, vararg labels: Label?) {
            foundTableSwitch = true
            super.visitTableSwitchInsn(min, max, dflt, *labels)
        }

        override fun visitEnd() {
            val hasStateMachine = foundGetLabel && foundTableSwitch
            if (filter.suspend(className, methodName, hasStateMachine)) {
                dumper.dump(className, methodName, methodDesc, true, hasStateMachine, access)
            }

            foundGetLabel = false
            foundTableSwitch = false

            super.visitEnd()
        }
    }

    companion object {
        @JvmStatic
        fun main(args: Array<String>) {
            val f = File("build/classes/kotlin/main")
            StateMachineChecker().processDir(f)
        }
    }
}