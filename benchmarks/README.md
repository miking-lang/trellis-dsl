## Trellis Benchmarks

This directory contains the necessary tools to run the Trellis benchmark suite.

### Requirements

Running the benchmarks requires an Nvidia GPU with drivers for CUDA 11.7. We provide an Anaconda file `condaenv-trellis.yml` for installing the required versions of Python, CUDA, and pomegranate (version 1.0.4), as well as packages used to produce plots.

The benchmarks compares Trellis against existing tools, which require a manual installation. This includes the configuration of zipHMM, StochHMM, and the native CUDA implementation (KTHDNA), the first of which is included as a submodule that can be initialized as follows:

```
git submodule init
git submodule update
```

For zipHMM (`forward/ziphmm/ziphmm`), the project needs to be built by following the instructions of their README, so that the provided symlinks in `forward/ziphmm` refer to existing files. Specifically, this includes running `cp zipHMM/libpyZipHMM.so zipHMM/pyZipHMM/` from the root of that repository to match the symlink used in the benchmark runner.

To build KTHDNA (`viterbi/native-cuda/KTHDNA`) you can run `make`. It requires `nvcc` to be installed and in the PATH and the `libhdf5-dev` package. Note that it does not work to install in a conda environment if the `hdf5` package is installed.

To install StochHMM (`https://github.com/KorfLab/StochHMM`), follow the instructions provided in the README to produce an executable. The path of the produced binary `stochhmm` must be added to the `$PATH` so that the runner script can find it.

### Running the Benchmarks

To run the benchmarks, activate the Anaconda environment (`conda activate trellis-bench`) and run the benchmark script (`./run.sh`) from the root of the benchmark directory. This command runs all the benchmarks, storing the intermediate results in the `out/` directory, and produces result plots in the current working directory.

### Validating the Results

The results produced by the different tools vary slightly. As the more significant differences are found for the weather model results, where we use significantly longer observation sequences, we believe this is due to differences in numerical precision. First, operations on floating-point numbers are non-associative, meaning the result may differ when executing sequentially and in parallel. Second, Trellis uses 32-bit floats in our benchmarks, while other tools may use other representations, such as 64-bit floats (which have better precision but are significantly slower on GPUs). For instance, we can see this in Trellis' results, which closely follow that of the sparse pomegranate approach, while the dense pomegranate approach gives a noticeably different result.

For the Forward algorithm, we provide a script `scripts/cmp-forward.py`. It prints the probabilities computed by the respective tools when running the benchmark script on the weather and 3mer models in a table. Each row of the table represents the probability reported by the tool (in logarithmic scale) of the respective column (as determined by the header). We see that pomegranate's sparse and dense approaches give the same results regardless of whether they run on the CPU or the GPU, and that Trellis' results are similar to that of the sparse pomegranate version. Overall, we find that the differences are quite small, especially for the 3mer model where the observation sequence is much shorter.

For the Viterbi algorithm, we provide a script `scripts/cmp-viterbi.py`. This script computes the probability of the resulting state sequence reported by the Viterbi algorithm for the weather model, and prints these in a table in a similar fashion as for the Forward algorithm. We find that Trellis consistently reports a more likely state sequence - it seems as if StochHMM misbehaves for some sequences, due to the irregular probabilities (a few are in line with Trellis while others are way less likely). To compare the results for the 3mer model, we interpret the nucleotide sequence estimated by each tool and compare their edit distances pairwise using the [Levenshtein distance](https://en.wikipedia.org/wiki/Levenshtein_distance) algorithm. For these results, we find that the three approaches are really close without batching (a difference of 200 means an average of 2 nucleotides differing per observation sequence) and that the native CUDA implementation is fairly close to Trellis with batching enabled, but that there are more differences there.
