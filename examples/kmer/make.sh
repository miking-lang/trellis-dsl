#!/bin/sh

MODEL_PATH=../../benchmarks/models/3mer.hdf5
SIGNAL_PATH=../../benchmarks/signals/kmer.hdf5

case $1 in
  build)
    trellis kmer.trellis
    ;;
  run)
    python3 runner.py $MODEL_PATH $SIGNAL_PATH
    ;;
  clean)
    rm -rf hmm.cu trellis.py __pycache__ __init__.py
    ;;
  *)
    >&2 echo "Expected argument 'build', 'run' or 'clean'"
    exit 1
    ;;
esac
