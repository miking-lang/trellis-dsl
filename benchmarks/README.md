## Trellis Benchmarks

This directory contains the necessary tools to run the Trellis benchmark suite.

### Requirements

Running the benchmarks requires an Nvidia GPU with drivers for CUDA 11.7. We provide an Anaconda file `condaenv-trellis.yml` for installing the required versions of Python, CUDA, and pomegranate (version 1.0.4), as well as packages used to produce plots.

The benchmarks compares Trellis against existing tools, which require a manual installation. This includes the configuration of zipHMM, StochHMM, and the native CUDA implementation (KTHDNA), which are included as submodules. These can be initialized as follows:

```
git submodule init
git submodule update
```

For zipHMM (`forward/ziphmm/ziphmm`), the project needs to be built by following the instructions of their README, so that the provided symlinks in `forward/ziphmm` refer to existing files. Specifically, this includes running `cp zipHMM/libpyZipHMM.so zipHMM/pyZipHMM/` from the root of that repository to match the symlink used by the benchmark runner.

To build KTHDNA (`viterbi/native-cuda/KTHDNA`) you can run `make`. It requires `nvcc` to be installed and in the PATH and the `libhdf5-dev` package. Note that it does not work to install in a conda environment if the `hdf5` package is installed.

To install StochHMM (`https://github.com/KorfLab/StochHMM`), follow the instructions provided in the README to produce an executable. The path of the produced binary `stochhmm` must be added to the `$PATH` so that the runner script can find it.

### Running the Benchmarks

To run the benchmarks, activate the Anaconda environment (`conda activate trellis-bench`) and run the benchmark script (`./run.sh`) from the root of the benchmark directory. This command runs all the benchmarks, storing the intermediate results in the `out/` directory, and produces result plots in the current working directory.

### Validating the Results

The results produced by Trellis and the other tools differ slightly. We believe the majority of these differences are due to differences in precision of floating-point numbers. First, operations on floating-points are non-associative, so the order in which operations are performed may differ when executing sequentially and in parallel. Second, Trellis uses 32-bit floats by default (this is what we use in the benchmarks), while other tools may use other representations (e.g., 64-bit floats which have better precision but are slower on GPUs).

For the Forward algorithm, we provide the script `scripts/cmp-forward.py`. It compares the output files produced when running the benchmark script (on the weather and 3mer models) in a pairwise fashion. For every pair, the script computes the arithmetic mean and the standard deviation of the absolute difference between the probabilities reported by the two tools, as well as the total difference.

For the Viterbi algorithm, we provide the script `scripts/cmp-viterbi.py`. This script first compares the output of the weather model, where we compare the probabilities of the reported state sequence in a similar fashion as for the Forward algorithm. We do this because the simplicity of the model means many distinct state sequences will have very similar probability. Second, the script compares the 3mer model results of each tool, by computing the [Levenshtein distance](https://en.wikipedia.org/wiki/Levenshtein_distance) of the nucleotide sequence represented by the resulting state sequences. In this case, we see that the results are very similar across all versions.
