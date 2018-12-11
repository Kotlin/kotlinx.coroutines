# Reference documentation site

This module builds references documentation.

## Building

* Install [Jekyll](http://jekyllrb.com)
* If you already have Ruby/Jekyll installed you might need to update its version:
  * `cd site/docs`
  * `bundle install`
* In project root directory do:
  * Run `./gradlew site`
* The result is in `site/build/gh-pages/_site`
* Upload it to github pages (`gh-pages` branch) 
