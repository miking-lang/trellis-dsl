#!/bin/sh

case $1 in
  build)
    trellis weather.trellis
    ;;
  run)
    python3 runner.py
    ;;
  clean)
    rm -rf hmm.cu libhmm.so trellis.py __pycache__ pred*.npy
    ;;
  *)
    >&2 echo "Expected argument 'build', 'run' or 'clean'"
    exit 1
    ;;
esac
