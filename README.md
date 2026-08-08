# Arlib

A curated, **mathlib-style** library of reusable Lean 4 + Mathlib results,
distilled from the meelgroup formalization projects. The goal is a single,
clean, `sorry`-free library that others can `import` and build on — rather than
re-proving the same infrastructure in every new project.


## Design philosophy

Emulating Mathlib: general, reusable content lives here under a single root
namespace (`Arlib`), organized by mathematical area, with docstrings and a root
module that re-exports everything. Project-specific *capstone* theorems (the
correctness proof of a particular algorithm) stay in their own repositories;
Arlib holds the **general lemmas underneath them** that are worth sharing.

Each area is a directory `Arlib/<Area>/` with an area root `Arlib/<Area>.lean`
that re-exports the area's modules. The library root `Arlib.lean` re-exports all
area roots, so `import Arlib` gives you everything and `import Arlib.Probability`
gives you one area.


## Build

Pinned to **Lean `v4.15.0`** and **Mathlib `v4.15.0`** (same as the source
projects, so material migrates with zero porting).

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (don't compile Mathlib from source)
lake build           # builds everything; the root re-exports every area
```

`import Arlib` in your own file to use the library.



## Layout

```
arlib/                    # repo folder (Lake package name stays lowercase)
  lean-toolchain          # leanprover/lean4:v4.15.0
  lakefile.toml           # requires mathlib @ v4.15.0
  Arlib.lean              # library root — re-exports every area
  Arlib/
    Prelude.lean
    Probability.lean      # area root — re-exports the modules below
    Probability/*.lean
    Combinatorics.lean    # area root
    Combinatorics/*.lean  # Finset, BigOperators, ListFold
    Approximation.lean            # area root
    Approximation/MulError.lean   # multiplicative error windows
    Approximation/Coresets/*.lean # Basic, Embedding, Tensor, Linear, RegionTree
    Approximation/StructuredCircuit.lean # v-trees and structured circuits
    MarkovChains.lean     # area root
    MarkovChains/
      Techniques/*.lean   # machinery valid for any finite chain
      Chains/*.lean       # analysis of specific chains
    KnowledgeCompilation.lean   # area root
    KnowledgeCompilation/
      Circuits/*.lean       # the representation languages themselves
      Communication/*.lean  # rectangles and the complexity measures
      LowerBounds/*.lean    # the bridge, the lifting, the separations
      BranchingPrograms/*.lean  # NROBP size lower bounds via matching width
      Forgetting/*.lean     # compiling DNNF by forgetting auxiliary variables
      Tseitin/*.lean        # DNNF lower bounds for Tseitin formulas
    Automata.lean         # area root
    Automata/*.lean       # NFA/DFA/UFA, and state lower bounds via communication
    Algorithms.lean       # area root
    Algorithms/TPA/*.lean # the Tootsie Pop Algorithm
    InformationTheory.lean    # area root
    InformationTheory/*.lean  # entropy, chain rule, Fano, query lower bounds
    GameTheory.lean       # area root
    GameTheory/*.lean     # Yao's minimax principle
    MDP.lean              # area root
    MDP/*.lean            # finite MDPs with reachability objectives
```

## License

Released under the [Apache License 2.0](LICENSE), following Mathlib. Copyright ©
2026 Kuldeep S. Meel.

## Acknowledgements

Built with the assistance of **Claude** (Anthropic's Claude Code).
