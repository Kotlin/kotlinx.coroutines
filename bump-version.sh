#!/bin/sh

set -efu

# the list of files that need to have the version updated in them
#
# limitations:
# * no newlines in names
# * no ' char in names
files="
README.md
kotlinx-coroutines-core/README.md
kotlinx-coroutines-debug/README.md
kotlinx-coroutines-test/README.md
ui/coroutines-guide-ui.md
gradle.properties
integration-testing/gradle.properties
"

# read gradle.properties to get the old version
set +e
old_version="$(git grep -hoP '(?<=^version=).*(?=-SNAPSHOT$)' gradle.properties)"
set -e
if [ "$?" -ne 0 ]
  then
    echo "Could not read the old version from gradle.properties." >&2
    if [ "$#" -ne 2 ]
      then
        echo "Please use this form instead: ./bump-version.sh old_version new_version"
        exit 1
    fi
fi

# check the command-line arguments for mentions of the version
if [ "$#" -eq 2 ]
  then
    echo "If you want to infer the version automatically, use the form: ./bump-version.sh new_version" >&2
    if [ -n "$old_version" -a "$1" != "$old_version" ]
      then
        echo "The provided old version ($1) is different from the one in gradle.properties ($old_version)." >&2
        echo "Proceeding anyway with the provided old version." >&2
    fi
    old_version=$1
    new_version=$2
  elif [ "$#" -eq 1 ]
  then
    new_version=$1
  else
    echo "Use: ./bump-version.sh new_version" >&2
    exit 1
fi


# Escape dots, e.g. 1.0.0 -> 1\.0\.0
escaped_old_version="$(printf "%s\n" "$old_version" | sed 's/[.]/\\./g')"

update_version() {
    file=$1
    to_undo=$2
    echo "Updating version from '$old_version' to '$new_version' in $1" >&2
    if [ -n "$(git diff --name-status -- "$file")" ]
      then
        printf "There are unstaged changes in '$file'. Refusing to proceed.\n" >&2
        [ -z "$to_undo" ] || eval "git checkout$to_undo"
        exit 1
    fi
    sed -i.bak "s/$escaped_old_version/$new_version/g" "$file"
    rm -f "$1.bak"
}

to_undo=$(printf "%s" "$files" | while read -r file; do
    if [ -n "$file" ]
      then
        update_version "$file" "${to_undo:-}"
        to_undo="${to_undo:-} '$file'"
        echo -n " '$file'"
    fi
done)

set +e
version_mentions=$(
    find . -type f \( -iname '*.properties' -o -iname '*.md' \) \
    -not -iname CHANGES.md \
    -exec git grep --fixed-strings --word "$old_version" {} +
    )
set -e
if [ -z "$version_mentions" ]
then
    echo "Done. To undo, run this command:" >&2
    printf "git checkout%s\n" "$to_undo" >&2
else
    echo "ERROR: Previous version is present in the project: $version_mentions"
    [ -z "$to_undo" ] || eval "git checkout$to_undo"
    exit 1
fi
