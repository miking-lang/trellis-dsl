# Trellis

The domain-specific language (DSL) Trellis for defining sparse hidden Markov
models.

## Installation

Trellis is implemented in [Miking](htpps//github.com/miking-lang/miking), which
needs to be installed in order to build the Trellis compiler. Also, in order to
compile (and to run) a Trellis model, CUDA needs to be installed. Finally, the
Python wrapper of Trellis expects to be passed NumPy arrays as arguments, which
requires Python and NumPy to be installed.

In order to build the project, the `MCORE_LIBS` environment variable needs to
specify the path to the Miking standard library, e.g.,
```
export MCORE_LIBS="$(HOME)/.local/lib/mcore/stdlib"
```

Run `make` in the project root to build the Trellis compiler, producing a
binary `build/trellis`. Optionally, use `make install` to install the compiler
under `$(HOME)/.local/bin` and install the source files to
`$(HOME)/.local/src/trellis`.

To run all unit tests defined in the Trellis compiler, use `make test`.

## Examples

See the `examples` directory for concrete examples of how to use Trellis. In
each example directory, we include a Trellis model (with the `.trellis`
suffix), a Python script importing the generated Trellis library and using it
(`runner.py`), and a script to build and run the example as well as clean up
the directory (`make.sh`).

## Usage

The Trellis compiler produces a Python interface to CUDA code for a model
specified in a Trellis file. We generate this interface for a model stored in
`test.trellis` by running `trellis <options> test.trellis` (to get a list of
available options, run `trellis --test`). The Trellis compiler produces the
following files:
1. A CUDA source file containing the generated model code (`hmm.cu`).
2. A shared library for the CUDA source file, that is loaded by the Python
   wrapper (`libhmm.so`).
3. A Python wrapper file which performs calls to the shared library
   (`trellis.py`).
4. When precomputing predecessors, it also produces one or more files with
   extension `.npy` containing the precomputed predecessor values.

The Python wrapper defines a Python class `HMM`. The constructor of this class
takes a dictionary with an entry corresponding to each table declared in the
Trellis model. The current HMM interface defines two methods:
1. `forward(obs)` applies the [Forward algorithm](https://en.wikipedia.org/wiki/Forward_algorithm)
to a provided list of observation sequences in parallel. The result is a list
of floating-point values representing the probability of the most likely
sequence of states (in logarithmic scale).
2. `viterbi(obs, num_parallel=1)` applies the [Viterbi algorithm](https://en.wikipedia.org/wiki/Viterbi_algorithm)
to a provided list of observation sequences, using the specified amount of
parallelism. The result is a list containing the most likely sequence of states
for each provided input. The `num_parallel` argument determines the number of
observation sequences that are processed in parallel on the GPU and, therefore,
indirectly controls how much GPU memory is used.

### Encoding

States and observations are mapped to integers using a [mixed
radix](https://en.wikipedia.org/wiki/Mixed_radix) numeral system. The generated
Trellis code uses the encoded integer values to represent states and
observations. However, the generated Python wrapper does not support
automatically converting a high-level specification of states to the low-level
integer encoding. Therefore, users have to automatically convert states and
observations to integer values. This could be improved in the future.

A state (or an observation) in Trellis is either a single finite type (a data
type or a bounded integer) or a tuple consisting of multiple (finite) types.
As all components of a state are finite, they can be mapped to integer values.

For a tuple, we treat each component as an integer value between 0 and the
number of possible values (exclusive), and we encode these as a mixed radix
system with the rightmost component in declaration order representing the least
significant value.

The bounded integer type `a..b` in Trellis represents the integers between `a`
(inclusive) and `b` (inclusive). We encode this as an integer value by
subtracting its lower bound `a`.

For a data type we map each constructor to an increasing integer value starting
from zero. For example, if we have a Trellis data type `type State = { A, B }`,
then `A` is mapped to 0 and `B` is mapped to 1, and `State` is treated as the
bounded integer type `0..1`.

See the examples in `examples/` for concrete use cases where this encoding has
been performed.
