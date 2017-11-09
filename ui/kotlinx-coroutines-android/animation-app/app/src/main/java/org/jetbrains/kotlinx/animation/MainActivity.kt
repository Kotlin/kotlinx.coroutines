package org.jetbrains.kotlinx.animation

import android.arch.lifecycle.ViewModelProviders
import android.os.Bundle
import android.support.v7.app.AppCompatActivity
import kotlinx.android.synthetic.main.activity_main.*
import kotlinx.android.synthetic.main.content_main.*

class MainActivity : AppCompatActivity() {
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)
        setSupportActionBar(toolbar)

        val animationModel = ViewModelProviders.of(this).get(AnimationModel::class.java)
        animationModel.observe(this, animationView)

        addButton.setOnClickListener {
            animationModel.addAnimation()
        }

        removeButton.setOnClickListener {
            animationModel.clearAnimations()
        }
    }
}
