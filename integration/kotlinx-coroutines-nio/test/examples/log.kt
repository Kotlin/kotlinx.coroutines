/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.examples

import java.text.SimpleDateFormat
import java.util.*

fun log(msg: String) = println("${SimpleDateFormat("yyyyMMdd-HHmmss.sss").format(Date())} [${Thread.currentThread().name}] $msg")