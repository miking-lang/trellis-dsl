#!/bin/bash

NSIGNALS=100
WEATHER_SIGNAL_LENGTH=1000000
NITERS=10
KMER_MODELS=("$(pwd)/models/3mer.hdf5" "$(pwd)/models/5mer.hdf5" "$(pwd)/models/7mer.hdf5")
KMER_LENGTH=(3 5 7)

bench_program() {
  hyperfine -i --warmup 1 --runs $NITERS -u second --export-json $2 "$1"
}

bench_ziphmm() {
  CMD="python3 run.py >> $(pwd)/out/z-$1-forward.txt 2>> $(pwd)/out/ziphmm-$1-log.txt"
  OUT_PATH="$(pwd)/out/z-$1-forward.json"
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
  CMD="python3 forward/pomegranate/run.py $1 $3 >> $(pwd)/out/${TARGET_ID}-$2-forward.txt 2>> $(pwd)/out/pomegranate-$3-log.txt"
  OUT_PATH="$(pwd)/out/${TARGET_ID}-$2-forward.json"
  bench_program "$CMD" "$OUT_PATH"
}

bench_trellis_forward() {
  CMD="python3 run.py >> $(pwd)/out/$1-forward.txt 2>> $(pwd)/out/trellis-forw-$1-log.txt"
  OUT_PATH="$(pwd)/out/$1-forward.json"
  cd forward/trellis
  bench_program "$CMD" "$OUT_PATH"
  cd ../..
}

bench_stochhmm() {
  # To make it use consistent naming with other 3mer tests running without
  # batching enabled
  if [ "$1" == "3mer" ]
  then
    OUT_ID="$1-nobatch"
  else
    OUT_ID="$1"
  fi
  CMD="stochhmm -model $1.hmm -seq $SIGNALS_PATH -viterbi -gff >> $(pwd)/out/stochhmm-$1-log.txt"
  OUT_PATH="$(pwd)/out/s-$OUT_ID-viterbi.json"
  cd viterbi/stoch-hmm
  bench_program "$CMD" "$OUT_PATH"
  cd ../..
}

bench_cuda() {
  TARGET="$1mer"
  if [ $2 -eq 1024 ]
  then
    TEST_ID="$TARGET-batch"
  else
    TEST_ID="$TARGET-nobatch"
  fi
  CMD="python3 run.py $1 $2 >> $(pwd)/out/n-$TEST_ID-viterbi.txt 2>> $(pwd)/out/native-$1mer-log.txt"
  OUT_PATH="$(pwd)/out/n-$TEST_ID-viterbi.json"
  cd viterbi/native-cuda
  bench_program "$CMD" "$OUT_PATH"
  cd ../..
}

bench_trellis_viterbi() {
  if [ -z ${2+x} ]
  then
    TEST_ID="$1"
  else
    if [ $3 -eq 1024 ]
    then
      TEST_ID="$1-batch"
    elif [ $3 -eq 8885 ]
    then
      TEST_ID="$1-nobatch"
    fi
  fi
  CMD="python3 run.py $2 >> $(pwd)/out/${TEST_ID}-viterbi.txt 2>> $(pwd)/out/trellis-vit-$2-log.txt"
  OUT_PATH="$(pwd)/out/${TEST_ID}-viterbi.json"
  cd viterbi/trellis
  bench_program "$CMD" "$OUT_PATH"
  cd ../..
}

bench_compile_trellis() {
  if [ $2 -eq 0 ]
  then
    TEST_PREFIX="tr"
    ARGS="--error-predecessor-analysis"
  else
    TEST_PREFIX="tc"
    ARGS="--force-precompute-predecessors"
  fi
  CMD="trellis ${ARGS} $1.trellis"
  OUT_PATH="$(pwd)/out/${TEST_PREFIX}-$1-compile.json"
  cd viterbi/trellis

  # If the initial compilation fails, we skip running the compiler evaluation
  # for this configuration.
  $CMD > /dev/null 2> /dev/null
  if [ $? -eq 0 ]
  then
    bench_program "$CMD" "$OUT_PATH"
  fi
  cd ../..
}

compile_trellis() {
  cd $1/trellis
  trellis $3 "$2.trellis"
  cd ../..
}

if [ ! -e "signals/weather.fasta" -o ! -e "signals/weather.hdf5" -o ! -e "signals/kmer.fasta" ]
then
  echo "Generating weather observation sequences and translating signals to StochHMM format"
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
compile_trellis "forward" "weather"
bench_trellis_forward "tc-weather"

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
compile_trellis "forward" "3mer" "--force-precompute-predecessors"
bench_trellis_forward "tc-3mer"
compile_trellis "forward" "3mer"
bench_trellis_forward "tr-3mer"

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
compile_trellis "viterbi" "weather"
bench_trellis_viterbi "tc-weather"

echo "############################"
echo "# KMER MODEL (NO BATCHING) #"
echo "############################"

# StochHMM segfaults for 5-mer model, so we only run 3-mer (it's clear our
# approach is faster, regardless)
BATCH_SIZE=8885
BATCH_OVERLAP=0
TRELLIS_BATCH="--batch-size $BATCH_SIZE --batch-overlap $BATCH_OVERLAP"
export MODEL_PATH=${KMER_MODELS[0]}
export SIGNALS_PATH="$(pwd)/signals/kmer.fasta"
bench_stochhmm "3mer"
export SIGNALS_PATH="$(pwd)/signals/kmer.hdf5"
bench_cuda 3 $BATCH_SIZE
compile_trellis "viterbi" "3mer" "$TRELLIS_BATCH --force-precompute-predecessors"
bench_trellis_viterbi "tc-3mer" 3 $BATCH_SIZE
compile_trellis "viterbi" "3mer" "$TRELLIS_BATCH"
bench_trellis_viterbi "tr-3mer" 3 $BATCH_SIZE

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
  bench_cuda $K $BATCH_SIZE
  compile_trellis "viterbi" "${K}mer" "$TRELLIS_BATCH --force-precompute-predecessors"
  bench_trellis_viterbi "tc-${K}mer" $K $BATCH_SIZE
  compile_trellis "viterbi" "${K}mer" "$TRELLIS_BATCH"
  bench_trellis_viterbi "tr-${K}mer" $K $BATCH_SIZE
done

echo "##########################"
echo "# COMPILATION BENCHMARKS #"
echo "##########################"
# Benchmarks specifically for the Trellis compilation performance. We both run
# the compiler normally and with a flag that forces it to precompute all
# predecessors at compile-time.

# Measure with and without predecessor computations and using either CPU or GPU
# as the target.
for i in 0 1
do
  bench_compile_trellis "weather" "$i"
  bench_compile_trellis "3mer" "$i"
  bench_compile_trellis "5mer" "$i"
  bench_compile_trellis "7mer" "$i"
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
TRELLIS_CLEAN="hmm.cu pred*.npy trellis.py __pycache__"

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
