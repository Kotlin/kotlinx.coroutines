package kotlinx.coroutines.experimental.firebase.android.app

import android.support.test.runner.AndroidJUnit4
import com.google.firebase.FirebaseException
import com.google.firebase.database.*
import kotlinx.coroutines.experimental.firebase.android.pushValue
import kotlinx.coroutines.experimental.firebase.android.readList
import kotlinx.coroutines.experimental.firebase.android.readValue
import kotlinx.coroutines.experimental.firebase.android.saveValue
import kotlinx.coroutines.experimental.runBlocking
import org.hamcrest.Matchers.*
import org.junit.Assert.assertThat
import org.junit.Assert.fail
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class DatabaseReferenceIntegrationTest : BaseIntegrationTest() {

    @Test
    fun testStringCanBeManipulated() = runBlocking {
        val messagesNode = FirebaseDatabase.getInstance().getReference("tasks")

        val firstMessageNode = messagesNode.child("1")
        val secondMessageNode = messagesNode.child("2")
        val thirdMessageNode = messagesNode.child("3")

        try {
            firstMessageNode.saveValue("Call Mary tomorrow morning")
            secondMessageNode.saveValue("See the new TV show season")
            thirdMessageNode.saveValue("Spread Kotlin word")

            val first = firstMessageNode.readValue<String>()
            val second = secondMessageNode.readValue(String::class.java)
            val third = messagesNode.orderByValue().limitToFirst(1).readList<String>()

            assertThat(third.size, `is`(equalTo(1)))
            assertThat(third[0], `is`(equalTo("Call Mary tomorrow morning")))
            assertThat(first, `is`(equalTo("Call Mary tomorrow morning")))
            assertThat(second, `is`(equalTo("See the new TV show season")))
        } catch (exception: FirebaseException) {
            fail("An exception should not be thrown here: ${exception.message}")
        }

        /* return */ Unit
    }

    @Test
    fun testDataClassWithSimpleObjectsCanBeManipulated() = runBlocking {
        val carsNode = FirebaseDatabase.getInstance().getReference("cars")

        val leyland = Car("Leyland Mini 1000", 1959, 8350.0)
        val mustang = Car("Ford Mustang", 1970, 65200.0)
        val fpace = Car("Jaguar F-Pace", 2017, 549999.0)

        try {
            carsNode.pushValue(leyland)
            carsNode.pushValue(mustang)
            carsNode.pushValue(fpace)

            val carsRetrieved = carsNode.readList<Car>()

            assertThat(carsRetrieved.size, `is`(equalTo(3)))
            assertThat(carsRetrieved, hasItem(leyland))
            assertThat(carsRetrieved, hasItem(mustang))
            assertThat(carsRetrieved, hasItem(fpace))
        } catch (exception: FirebaseException) {
            fail("An exception should not be thrown here: ${exception.message}")
        }

        /* return */ Unit
    }

    private data class Car(
            val model: String = "",
            val releaseYear: Int = 0,
            val price: Double = 0.0)

}
