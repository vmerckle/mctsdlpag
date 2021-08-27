# Dependency

DL-PA Parser&Grounder https://github.com/AbdallahS/dlpag

# Usage

    dune exec mydlpag [file]

Or

    dune install
    mctsdlpag [formula file]

# Example usage

		mctsdlpag encodings/hanoi.pa --solver MCDS --quicksolver propositional -c 0.3

# Options

    DL-PA Solver
    Usage : mctsdlpag <dlpa file>
      --quicksolver Quicksolver to use : propositional, allbutkleene, deterministic, smallsize, neversmall
      --solver Solver to use : MCTS, MCDS, simple
      -c UCT's constant
      -v Output debug information
      -help  Display this list of options
      --help  Display this list of options
