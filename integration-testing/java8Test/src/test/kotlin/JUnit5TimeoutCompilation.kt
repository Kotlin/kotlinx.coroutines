import kotlinx.coroutines.debug.junit5.CoroutinesTimeout
import org.junit.jupiter.api.*

class JUnit5TimeoutCompilation {
    @CoroutinesTimeout(1000)
    @Test
    fun testCoroutinesTimeoutNotFailing() {
    }
}
