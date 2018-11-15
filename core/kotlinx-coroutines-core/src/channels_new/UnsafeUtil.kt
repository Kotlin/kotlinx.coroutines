package channels_new

import sun.misc.Unsafe

object UtilUnsafe {
    val unsafe: Unsafe
        get() {
            if (UtilUnsafe::class.java.classLoader == null)
                return Unsafe.getUnsafe()
            try {
                val fld = Unsafe::class.java.getDeclaredField("theUnsafe")
                fld.isAccessible = true
                return fld.get(UtilUnsafe::class.java) as Unsafe
            } catch (e: Exception) {
                throw RuntimeException("Could not obtain access to sun.misc.Unsafe", e)
            }
        }
}