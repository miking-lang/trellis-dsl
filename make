#!/bin/sh

test () {
  set +e
  compile_cmd="build/main"
  output=$1
  output="$output\n$($compile_cmd $1 2>&1)"
  exit_code=$?
  if [ $exit_code -ne 0 ]
  then
    echo "ERROR: command '$compile_cmd $1 2>&1' exited with $exit_code"
    echo "$output"
    exit 1
  fi
  echo "$output\n"
  set -e
}

case $1 in
  test)
    test "$2"
    ;;
  *)
    >&2 echo "Incorrect argument"
    exit 1
    ;;
esac
