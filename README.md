# trellis-dsl
The Trellis DSL for handling Hierarchical hidden Markov models

## Building

To build the project, [Miking](https://github.com/miking-lang/miking) must be
installed, and the `MCORE_STDLIB` environment variable must be the path to the
Miking `stdlib` (please see the [Miking
README](https://github.com/miking-lang/miking#getting-started)).

Run `make` in the project root to build the project. This creates a main binary
`build/main`. Run `make test` to run the test suite.
