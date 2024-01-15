#!/bin/sh

MODEL_PATH=../synthetic_dna/model/Params3_true.h5
SIGNAL_PATH=../synthetic_dna/data/signals100_1.fast5

# Produce the input files we pass to the generated executable
python3 parse.py $MODEL_PATH $SIGNAL_PATH

# Output text files from the parsing program
OUTPROB=output-prob.txt
INITPROB=initial-prob.txt
TRANS1=trans1.txt
TRANS2=trans2.txt
GAMMA=gamma.txt
INPUT_SIGNALS=input-signals.txt

# Run the executable passing the input files
./main --output-prob $OUTPROB --initial-prob $INITPROB --trans1 $TRANS1 --trans2 $TRANS2 --gamma $GAMMA --input-signals $INPUT_SIGNALS
