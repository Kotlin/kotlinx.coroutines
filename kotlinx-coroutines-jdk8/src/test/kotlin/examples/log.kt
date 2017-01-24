package examples

import java.text.SimpleDateFormat
import java.util.*

fun log(msg: String) = println("${SimpleDateFormat("YYYYMMdd-HHmmss.sss").format(Date())} [${Thread.currentThread().name}] $msg")