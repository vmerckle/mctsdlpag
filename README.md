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
      --solver Solver to use : MCTS, MCDS, simple, naive, MCDSn
      --nplayout Number of playout per expansion
      -c UCT's constant
      -v Output debug information
      -help  Display this list of options
      --help  Display this list of options

# Example encoding

    grounding:
    size := {1..180}.
    
    formula:
    psi := <ini><count \star> val(180).
    
    program:
    ini := val(0) <- \top.
    count := \bigcup I \in size : countto(I).
    \forall I \in size : countto(I) := ?val(I-1)? \seq val(I-1) <- \bot \seq val(I) <- \top.
    
    main:
    psi.
    
