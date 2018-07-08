package kotlinx.coroutines.experimental.firebase.android.app

import android.support.test.InstrumentationRegistry
import com.google.firebase.FirebaseApp
import com.google.firebase.auth.FirebaseAuth
import com.google.firebase.database.FirebaseDatabase
import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.firebase.android.await
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Before
import org.junit.BeforeClass

open class BaseIntegrationTest {

    companion object {
        @BeforeClass
        @JvmStatic
        fun setUpFirebaseAndContext() {
            val context = InstrumentationRegistry.getTargetContext()
            FirebaseApp.initializeApp(context)
        }
    }

    @Before
    fun tearDown() = runBlocking {
        cleanupAuth().await()
        clearDatabase().await()
        /* return */ Unit
    }

    private suspend fun cleanupAuth() = async {
        val auth = FirebaseAuth.getInstance()

        val userIsLogged = auth.currentUser != null

        if (userIsLogged) {
            auth.currentUser!!.delete().await()
            auth.signOut()
        }
    }

    private suspend fun clearDatabase() = async {
        FirebaseDatabase.getInstance().reference.setValue(null).await()
    }
}
