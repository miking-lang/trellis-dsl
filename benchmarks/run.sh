#!/bin/bash

NSIGNALS=100
WEATHER_SIGNAL_LENGTH=1000000
NITERS=10
KMER_MODELS=("$(pwd)/models/3mer.hdf5" "$(pwd)/models/5mer.hdf5" "$(pwd)/models/7mer.hdf5")
KMER_LENGTH=(3 5 7)

bench_program() {
  hyperfine --warmup 1 --runs $NITERS -u second --export-json $2 "$1"
}

bench_ziphmm() {
  CMD="python3 run.py >> $(pwd)/out/zc-$1-forward.txt"
  OUT_PATH="$(pwd)/out/zc-$1-forward.json"
  cd forward/ziphmm
  bench_program "$CMD" "$OUT_PATH"
  cd ../..
}

bench_pomegranate() {
  if [ $1 -eq 0 ]
  then
    TARGET_ID="pc"
  else
    TARGET_ID="pg"
  fi
  CMD="python3 forward/pomegranate/run.py $1 $3 >> $(pwd)/out/${TARGET_ID}-$2-forward.txt"
  OUT_PATH="$(pwd)/out/${TARGET_ID}-$2-forward.json"
  bench_program "$CMD" "$OUT_PATH"
}

bench_trellis_forward() {
  if [ $1 -eq 0 ]
  then
    TARGET_ID="tc"
  else
    TARGET_ID="tg"
  fi
  CMD="python3 forward/trellis/run.py $1 >> $(pwd)/out/${TARGET_ID}-$2-forward.txt"
  OUT_PATH="$(pwd)/out/${TARGET_ID}-$2-forward.json"
  bench_program "$CMD" "$OUT_PATH"
}

bench_compile_trellis_forward() {
  if [ $1 -eq 0 ]
  then
    TARGET="multicore"
    TARGET_ID="tc"
  else
    TARGET="cuda"
    TARGET_ID="tg"
  fi
  CMD="trellis $2 --futhark-target $TARGET $3.trellis"
  OUT_PATH="$(pwd)/out/${TARGET_ID}-forward-compile-$3.json"
  cd forward/trellis
  bench_program "$CMD" "$OUT_PATH"
  cd -
}

bench_stochhmm() {
  CMD="stochhmm -model $1.hmm -seq $SIGNALS_PATH -viterbi"
  OUT_PATH="$(pwd)/out/sc-$1-nobatch-viterbi.json"
  cd viterbi/stoch-hmm
  bench_program "$CMD" "$OUT_PATH"
  cd -
}

bench_cuda() {
  TARGET="$1mer"
  if [ $2 -eq 1024 ]
  then
    TEST_ID="$TARGET-batch"
  else
    TEST_ID="$TARGET-nobatch"
  fi
  CMD="python3 run.py $1 $2 >> $(pwd)/out/ng-$TEST_ID-viterbi.txt"
  OUT_PATH="$(pwd)/out/ng-$TEST_ID-viterbi.json"
  cd viterbi/native-cuda
  bench_program "$CMD" "$OUT_PATH"
  cd -
}

bench_trellis_viterbi() {
  if [ $1 -eq 0 ]
  then
    TARGET_ID="tc"
  else
    TARGET_ID="tg"
  fi
  if [ -z ${4+x} ]
  then
    TEST_ID="$2"
  else
    if [ $4 -eq 1024 ]
    then
      TEST_ID="$2-batch"
    elif [ $4 -eq 8885 ]
    then
      TEST_ID="$2-nobatch"
    fi
  fi
  CMD="python3 viterbi/trellis/run.py $3 $4 >> out/$TARGET_ID-$TEST_ID-viterbi.txt"
  OUT_PATH="$(pwd)/out/$TARGET_ID-$TEST_ID-viterbi.json"
  bench_program "$CMD" "$OUT_PATH"
}

bench_compile_trellis_viterbi() {
  if [ $1 -eq 0 ]
  then
    TARGET="multicore"
    TARGET_ID="tc"
  else
    TARGET="cuda"
    TARGET_ID="tg"
  fi
  CMD="trellis $2 --futhark-target $TARGET $3.trellis"
  OUT_PATH="$(pwd)/out/${TARGET_ID}-viterbi-compile-$3.json"
  cd viterbi/trellis
  bench_program "$CMD" "$OUT_PATH"
  cd -
}

if [ ! -e "signals/weather.fasta" -o ! -e "signals/weather.hdf5" -o ! -e "signals/kmer.fasta" ]
then
  echo "Generating weather observation sequences and translate signals to StochHMM format"
  python3 gen-signals.py $NSIGNALS $WEATHER_SIGNAL_LENGTH
fi

STOCH_3MER_MODEL="viterbi/stoch-hmm/3mer.hmm"
if [ ! -e $STOCH_3MER_MODEL ]
then
  echo "Generating 3mer model for StochHMM"
  export MODEL_PATH=${KMER_MODELS[0]}
  python3 viterbi/stoch-hmm/kmer-model-gen.py $STOCH_3MER_MODEL
fi

# Recreate the output directory, removing previous data
rm -rf out
mkdir -p out

echo "#####################"
echo "# FORWARD ALGORITHM #"
echo "#####################"

echo "#################"
echo "# WEATHER MODEL #"
echo "#################"

unset MODEL_PATH
export SIGNALS_PATH="$(pwd)/signals/weather.hdf5"
bench_ziphmm "weather"
bench_pomegranate 0 "weather"
bench_pomegranate 1 "weather"
bench_compile_trellis_forward 0 "--precompute-tables" "weather"
bench_trellis_forward 0 "weather"
bench_compile_trellis_forward 1 "--precompute-tables" "weather"
bench_trellis_forward 1 "weather"

echo "##############"
echo "# KMER MODEL #"
echo "##############"

# We only run 3-mer model because zipHMM is way too slow and pomegranate
# gets runtime errors because it fails handle the large state space.
export MODEL_PATH=${KMER_MODELS[0]}
export SIGNALS_PATH="$(pwd)/signals/kmer.hdf5"
bench_ziphmm "3mer"
bench_pomegranate 0 "3mer"
bench_pomegranate 1 "3mer"
bench_compile_trellis_forward 0 "--precompute-tables" "3mer"
bench_trellis_forward 0 "3mer"
bench_compile_trellis_forward 1 "--precompute-tables" "3mer"
bench_trellis_forward 1 "3mer"

echo "#####################"
echo "# VITERBI ALGORITHM #"
echo "#####################"

echo "#################"
echo "# WEATHER MODEL #"
echo "#################"
unset MODEL_PATH
export SIGNALS_PATH="$(pwd)/signals/weather.fasta"
bench_stochhmm "weather"
export SIGNALS_PATH="$(pwd)/signals/weather.hdf5"
bench_compile_trellis_viterbi 0 "--precompute-tables" "weather"
bench_trellis_viterbi 0 "weather"
bench_compile_trellis_viterbi 1 "--precompute-tables" "weather"
bench_trellis_viterbi 1 "weather"

echo "############################"
echo "# KMER MODEL (NO BATCHING) #"
echo "############################"

# StochHMM segfaults for 5-mer model, so we only run 3-mer (it's clear our
# approach is faster, regardless)
BATCH_SIZE=8885
BATCH_OVERLAP=0
TRELLIS_BATCH="--batch-size 8885 --batch-overlap 0"
export MODEL_PATH=${KMER_MODELS[0]}
export SIGNALS_PATH="$(pwd)/signals/kmer.fasta"
bench_stochhmm "3mer"
export SIGNALS_PATH="$(pwd)/signals/kmer.hdf5"
bench_cuda 3 $BATCH_SIZE
bench_compile_trellis_viterbi 0 "--precompute-tables $TRELLIS_BATCH" "3mer"
bench_trellis_viterbi 0 "3mer" 3 $BATCH_SIZE
bench_compile_trellis_viterbi 1 "--precompute-tables $TRELLIS_BATCH" "3mer"
bench_trellis_viterbi 1 "3mer" 3 $BATCH_SIZE

echo "#########################"
echo "# KMER MODEL (BATCHING) #"
echo "#########################"
BATCH_SIZE=1024
BATCH_OVERLAP=0
TRELLIS_BATCH="--batch-size $BATCH_SIZE --batch-overlap $BATCH_OVERLAP"
export SIGNALS_PATH="$(pwd)/signals/kmer.hdf5"

for i in $(seq 0 2)
do
  export MODEL_PATH=${KMER_MODELS[i]}
  K=${KMER_LENGTH[i]}
  if [ $K -eq 3 ]
  then
    TRELLIS_EXTRA_ARGS="--precompute-tables"
  else
    TRELLIS_EXTRA_ARGS=""
  fi
  bench_cuda $K $BATCH_SIZE
  bench_compile_trellis_viterbi 1 "$TRELLIS_EXTRA_ARGS $TRELLIS_BATCH" "${K}mer"
  bench_trellis_viterbi 1 "${K}mer" $K $BATCH_SIZE
done

echo "####################"
echo "# PLOTTING RESULTS #"
echo "####################"

# Plot compilation results
python3 scripts/plot-compile.py

# Plot results for the weather model
python3 scripts/plot-weather.py

# Plot results for the kmer model (with and without batching)
python3 scripts/plot-kmer.py

echo "###########"
echo "# CLEANUP #"
echo "###########"
TRELLIS_CLEAN="_generated* generated* __init__.py predecessors.txt __pycache__ trellis.py"

rm -f signals/weather.hdf5 signals/weather.fasta signals/kmer.fasta

cd forward/pomegranate
rm -rf __pycache__
cd ../..

cd forward/trellis
rm -rf $TRELLIS_CLEAN
cd ../..

cd forward/ziphmm
rm -rf __pycache__
cd ../..

cd viterbi/native-cuda
rm -rf __pycache__
cd ../..

cd viterbi/stoch-hmm
rm -rf __pycache__ 3mer.hmm 5mer.hmm
cd ../..

cd viterbi/trellis
rm -rf $TRELLIS_CLEAN
cd ../..
