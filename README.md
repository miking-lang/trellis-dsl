# Trellis

The domain-specific language (DSL) Trellis for defining sparse hidden Markov
models.

## Building

To build the project, [Miking](htpps//github.com/miking-lang/miking) must be
installed and the `MCORE_LIBS` environment variable must define the path to the
Miking standard library (TODO: this is currently not mentioned anywhere in the
documentation).

Run `make` in the project root to build the Trellis compiler, producing a
binary under `build/trellis`. Then, use `make install` to place the compiler
binary under `$(HOME)/.local/bin` and install source files to
`$(HOME)/.local/src/trellis`.

To run the test suite you can use `make test`.

## Usage

The Trellis compiler produces a Python interface to the generated Viterbi code
for the model specified in the Trellis source file. To compile a Trellis
program, you need to install [Futhark](https://futhark-lang.org/) and
the [futhark-ffi](https://pypi.org/project/futhark-ffi/) Python package.

The generated interface consists of a single function `viterbi`, which takes
two arguments:
1. A list of independent input signals which can be processed in parallel.
2. A record containing an entry for each table declared in the Trellis program,
   with the same dimensions as declared in Trellis.

The output from the `viterbi` function is the most likely sequence of states
for each input signal. We refer to the [examples](examples/) directory for
concrete examples of how to use the compiler.

TODO: automatically generate the predecessors

### Encoding of states

TODO: write about how we encode states. This is very important because the user
is responsible for mapping states to their integer representation when passing
inputs and similarly in the other direction when reading the output.
