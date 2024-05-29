#!/bin/sh

case $1 in
  build)
    trellis hallway.trellis
    ;;
  run)
    python3 runner.py
    ;;
  clean)
    rm -rf hmm.cu trellis.py __pycache__ pred*.npy
    ;;
  *)
    >&2 echo "Expected argument 'build', 'run' or 'clean'"
    exit 1
    ;;
esac
