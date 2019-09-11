/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

@file:JvmName("PerformanceTools")

package org.jetbrains.kotlin

import org.gradle.api.Project
import org.gradle.api.Task
import org.gradle.api.tasks.TaskState
import org.gradle.api.execution.TaskExecutionListener

fun getCompileTime(tasksNames: Iterable<String>, success: Boolean): String {
    var time = 0.0
    var status = true
    tasksNames.forEach {
        time += TaskTimerListener.getTime("$it")
        status = tasksNames.map { TaskTimerListener.tasksTimes.containsKey(it) }.reduce { a, b -> a && b }
        status = status && success
    }
    return "${if (status) "PASSED" else "FAILED"} $time"
}


// Class time tracker for all tasks.
class TaskTimerListener: TaskExecutionListener {
    companion object {
        val tasksTimes = mutableMapOf<String, Double>()
        fun getTime(taskName: String) = tasksTimes[taskName] ?: 0.0
    }

    private var startTime = System.nanoTime()

    override fun beforeExecute(task: Task) {
        startTime = System.nanoTime()
    }

    override fun afterExecute(task: Task, taskState: TaskState) {
        tasksTimes[task.name] = (System.nanoTime() - startTime) / 1000.0
    }
}

fun addTimeListener(subproject: Project) {
    subproject.gradle.addListener(TaskTimerListener())
}
