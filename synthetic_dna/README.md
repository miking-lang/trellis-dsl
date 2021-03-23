# sythetic_dna

Install the required third-party packages:  
```
python3 -m pip install -r install_python_pkgs.txt
```
## data overview


```
simulate_EDHMM_signals.py                     # python script generates a multireads_fast5 and its correspodning mapped_read.hdf5 file at each run

fakegenome.fa                                 # a randomly(uniform) generated DNA sequence
fakereference1000.fa                          # 1000 short DNA cuts from fakegenome.fa

data/                                         # contains the raw data of sythetic DNA
|
signals100_1.fast5                            # signal file
|
mapped_reads100_1.hdf5                        # training file contains signal, reference and its alignment information
|
signals100_2.fast5
|
mapped_reads100_2.hdf5

model/
|
Params3_true.h5                               # true model used to generate data/
|
ParamsInitK3L16.h5                            # initial model used for training


KTHDNA_viterbicall_result/                    # contains viterbi decoded sequence with perfect model Params3_true.hdf5
KTHDNA_viterbitrain_result/                   # contains BW trained model and their evaluation
|
evaluation/


install_python_pkgs.txt                       # lists the required Python packages
```
