/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This script is copied to "build" directory and run from there

const webpack = require("webpack");
const HtmlWebpackPlugin = require('html-webpack-plugin');
const UglifyJSPlugin = require('uglifyjs-webpack-plugin');
const path = require("path");

const dist = path.resolve(__dirname, "dist");

module.exports = {
    mode: "production",
    entry: {
        main: "main"
    },
    output: {
        filename: "[name].bundle.js",
        path: dist,
        publicPath: ""
    },
    devServer: {
        contentBase: dist
    },
    module: {
        rules: [
            {
                test: /\.css$/,
                use: [
                    'style-loader',
                    'css-loader'
                ]
            }
        ]
    },
    resolve: {
        modules: [
            path.resolve(__dirname, "kotlin-js-min/main"),
            path.resolve(__dirname, "kotlin-js-min/legacy/main"),
            path.resolve(__dirname, "../src/main/web/")
        ]
    },
    devtool: 'source-map',
    plugins: [
        new HtmlWebpackPlugin({
            title: 'Kotlin Coroutines JS Example'
        }),
        new UglifyJSPlugin({
            sourceMap: true
        })
    ]
};
