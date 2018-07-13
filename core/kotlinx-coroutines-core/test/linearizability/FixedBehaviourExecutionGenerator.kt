/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.execution.*
import java.util.*

typealias ExecutionBuilder = (List<MutableList<Actor>>, List<ActorGenerator>) -> Unit

/**
 * Example of usage:
 *
 * ```
 * StressOptions().injectExecution { actors, methods ->
 *   actors[0].add(actorMethod(methods, "receive1"))
 *   actors[0].add(actorMethod(methods, "receive2"))
 *
 *   actors[1].add(actorMethod(methods, "send2"))
 *   actors[1].add(actorMethod(methods, "send1"))
 * }
 *
 * ```
 *
 * Will produce
 * ```
 * Actors per thread:
 * [receive1(), receive2()]
 * [send2(), send1()]
 * ```
 * at the first iteration.
 *
 * DSL will be improved when this method will be used frequently
 */
fun Options<*, *>.injectExecution(behaviourBuilder: ExecutionBuilder): Options<*, *> {
    injectedBehaviour.add(behaviourBuilder)
    executionGenerator(FixedBehaviourInjectorExecutionGenerator::class.java)
    return this
}

fun actorMethod(generators: List<ActorGenerator>, name: String): Actor =
    generators.find { it.generate().method.name.contains(name) }?.generate() ?: error("Actor method $name is not found in ${generators.map { it.generate().method.name }}")

private val injectedBehaviour: Queue<ExecutionBuilder> = ArrayDeque<ExecutionBuilder>()

class FixedBehaviourInjectorExecutionGenerator(testConfiguration: CTestConfiguration, testStructure: CTestStructure)
    : ExecutionGenerator(testConfiguration, testStructure) {

    private val randomGenerator = RandomExecutionGenerator(testConfiguration, testStructure)

    override fun nextExecution(): List<List<Actor>> {
        val injector = injectedBehaviour.poll()
        if (injector != null) {
            val parallelGroup = ArrayList(testStructure.actorGenerators)
            val actorsPerThread = ArrayList<MutableList<Actor>>()
            for (i in testConfiguration.threadConfigurations.indices) {
                actorsPerThread.add(ArrayList())
            }

            injector.invoke(actorsPerThread, parallelGroup)
            return actorsPerThread
        }

        return randomGenerator.nextExecution()
    }
}

// Ad-hoc fixed execution injection for lin-checker
class FixedBehaviourExecutionGenerator(testConfiguration: CTestConfiguration, testStructure: CTestStructure)
    : ExecutionGenerator(testConfiguration, testStructure) {

    override fun nextExecution(): List<List<Actor>> {
        val parallelGroup = ArrayList(testStructure.actorGenerators)
        val actorsPerThread = ArrayList<MutableList<Actor>>()
        for (i in testConfiguration.threadConfigurations.indices) {
            actorsPerThread.add(ArrayList())
        }


        actorsPerThread[0].add(actorMethod(parallelGroup, "receive1"))
        actorsPerThread[0].add(actorMethod(parallelGroup, "receive2"))
        actorsPerThread[0].add(actorMethod(parallelGroup, "close1"))

        actorsPerThread[1].add(actorMethod(parallelGroup, "send2"))
        actorsPerThread[1].add(actorMethod(parallelGroup, "send1"))

        return actorsPerThread
    }
}