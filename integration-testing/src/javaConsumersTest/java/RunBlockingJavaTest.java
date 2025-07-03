import kotlinx.coroutines.BuildersKt;
import kotlinx.coroutines.Dispatchers;
import org.junit.Test;
import org.junit.Assert;

public class RunBlockingJavaTest {
    Boolean entered = false;

    /** This code will not compile if `runBlocking` doesn't declare `@Throws(InterruptedException::class)` */
    @Test
    public void testRunBlocking() {
        try {
            BuildersKt.runBlocking(Dispatchers.getIO(), (scope, continuation) -> {
                entered = true;
                return null;
            });
        } catch (InterruptedException e) {
        }
        Assert.assertTrue(entered);
    }
}
