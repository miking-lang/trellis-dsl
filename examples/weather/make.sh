#!/bin/sh

case $1 in
  build)
    trellis weather.trellis
    ;;
  run)
    python3 runner.py
    ;;
  clean)
    rm -rf *generated* trellis.py __init__.py __pycache__ predecessors.txt
    ;;
  *)
    >&2 echo "Expected argument 'build', 'run' or 'clean'"
    exit 1
    ;;
esac
