package kotlinx.coroutines.experimental.firebase.android.app

import android.support.test.runner.AndroidJUnit4
import com.google.firebase.auth.*
import kotlinx.coroutines.experimental.firebase.android.await
import kotlinx.coroutines.experimental.runBlocking
import org.hamcrest.Matchers.*

import org.junit.Test
import org.junit.runner.RunWith

import org.junit.Assert.assertThat
import org.junit.Assert.assertTrue
import org.junit.Assert.fail

@RunWith(AndroidJUnit4::class)
class TaskIntegrationTest : BaseIntegrationTest() {

    @Test
    fun testAwaitCanBeUsedToSignInAnonymously() = runBlocking {
        val auth = FirebaseAuth.getInstance()

        try {
            val account = auth.signInAnonymously().await()

            assertTrue(account.user.isAnonymous)
        } catch (exception: FirebaseAuthException) {
            fail("An exception should not be thrown here: ${exception.message}")
        }

        /* return */ Unit
    }

    @Test
    fun testAwaitCanBeUsedToGetAnAccessToken() = runBlocking {
        val auth = FirebaseAuth.getInstance()

        try {
            val account = auth.signInAnonymously().await()

            val forceRefresh = true
            val tokenResult = account.user.getIdToken(forceRefresh).await()

            assertThat(tokenResult.token, `is`(notNullValue()))
        } catch (exception: FirebaseAuthException) {
            fail("An exception should not be thrown here: ${exception.message}")
        }

        /* return */ Unit
    }

    @Test
    fun testAwaitCanBeUsedToCreateAnAccountWithBasicCredentials() = runBlocking {
        val auth = FirebaseAuth.getInstance()

        try {
            val (email, password) = "john@email.com" to "2cdf5fc7fc1c42dbead12584860f9c8a"
            val account = auth.createUserWithEmailAndPassword(email, password).await()

            val nameUpdate = UserProfileChangeRequest.Builder().setDisplayName("John Smith")
            account.user.updateProfile(nameUpdate.build()).await()

            assertThat(account.user.email, `is`(equalTo(email)))
            assertThat(account.user.displayName, `is`(equalTo("John Smith")))

            account.user.delete().await()
        } catch (exception: FirebaseAuthException) {
            fail("An exception should not be thrown here: ${exception.message}")
        }

        /* return */ Unit
    }
}
