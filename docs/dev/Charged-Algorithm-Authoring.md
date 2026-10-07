# Charged algorithm authoring for the complete 3sum construction

## Objective and fixed requirements

An algorithm author must be able to express the reduction, the shared matrix
encodings, pruned decoding and box preprocessing/query composition using
`Charged` operations over sealed data. `Charged.lean` is unchanged. Existing
clients remain valid. Every claimed machine cost needs a concrete RAM program
and a checked correspondence; a named operation or a `StdImpl` price is not
sufficient. No paper-specific matrix theorem is made a library primitive.

This work builds on the uncommitted, already verified realization, storage,
signed arithmetic and pooled-bucket work in this repository. The final commit
must include those dependencies and their regression tests, while leaving
unrelated `.claude/` and `writeup/` files untouched. Development attempts must be
preserved; no Git rollback is allowed.

## Design

Use the existing sealed `Word w` as the word-width-aware charged numeric carrier.
New charged word primitives live in `Machine.lean`: Lean private fields are
file-scoped, and a separate module cannot implement an observation without
breaking the seal. Their arguments and results are sealed words; comparisons
return already charged Boolean answers. Ordinary `Num` APIs are retained.

Sealed charged vectors contain mathematical word contents and a stored word
length. They are functional source models of mutable RAM buffers: writes return
updated source contents. Correctness certificates relate these contents to the
actual memory after stores. Retaining a stale source snapshot does not grant
permission to read an old physical version: composition must re-establish its
representation. Shared views used by the encoders are read-only while shared.
Forwarding register/handle metadata is free; inspection, copying, traversal,
allocation and arithmetic execute charged operations.

Introduce an exact realization certificate recording both result/state
correspondence and equality of the entire opcode vector. Its sequencing rule
threads representation through the updated RAM state. Equality transfers any
instruction pricing function, while separate checked source bounds transfer
unit-cost running time. Physical storage bounds continue to refer to actual RAM
allocation; this change does not identify a Charged profile with physical RAM.

Sealed-index loops perform the same initialization, guard and increment as their
RAM counterparts. Structural fuel is a coverage obligation, not an uncharged
runtime cardinality observation. Recursive algorithms can use these loops or an
explicit stack; allocation and frame invariants must be proved for scratch space.

## Implementation sequence and acceptance criteria

1. **Exact cost connection.** Add exact certificates, bind/consequence rules and
   conversion to `Realizes`. Prove pricing transfer for an arbitrary cost model.
2. **Charged words and storage.** Add literals, arithmetic, comparison and bounded
   word-vector allocation/read/write. Prove exact costs and RAM representations,
   including zero-sized allocation, invalid-index exclusions and wrapping words.
3. **Sealed-index iteration.** Add guarded early-exit iteration, correspondence
   with `wordRepeatWhile`, exact vector composition and complete-fuel examples.
   Do not expose raw natural indices to the author.
4. **Views and bulk operations.** Add indexed views, signed storage adapters,
   copying/filling and pointwise linear-combination traversal. Account for address
   arithmetic, overlap assumptions, initialization and shared read-only handles.
5. **Strings and enumeration.** Build finite-alphabet words on charged vectors.
   Provide symbol access/update, comparisons and incremental path/subset/box
   enumeration. Prove costs per visited/generated item; never scan the full
   string universe to enumerate a sparse family.
6. **Sparse collections and tries.** Use a pool of nodes and a constant alphabet
   transition table, with terminal occupancy separate from stored values. Lookup
   and insertion charge each traversed edge and newly allocated/initialized node.
   Prove finite paths, capacity rejection, duplicate insertion and lookup after
   update. Reserve capacity proportional to nodes, not all possible keys.
   Implement sparse grouping/deduplication/traversal with concrete bounds.
7. **Reusable arithmetic and recursive composition.** Supply charged integer
   parameter algorithms (ceiling division, power thresholds, square root and
   prime testing/enumeration), cyclic coefficient arithmetic, and recursion/stack
   composition sufficient to implement the paper's algorithms. Any intermediate
   word fit, sufficient scratch capacity and effective enumeration bounds must
   remain explicit.
8. **Adoption and review.** Explain which operations implement each paper step;
   add end-to-end examples that retain sharing and sparse work. Inspect installed
   APIs in writer guidance. No pin upgrade, completion gate or implicit borrowed
   implementation is added.

## Cost investigation

For each operation, inspect the executable body and prove its cost vector rather
than writing down a second tally. Check empty, singleton, boundary-width,
early-exit, failed-capacity, duplicate and absent-key cases. Inspect allocation
separately from live cardinality. Pay for every memory access and numeric test;
static finite-symbol dispatch can be control plumbing only after a charged symbol
read. Variable-length equality and ordering must charge traversal.

Views and tiles must preserve sharing: no hidden materialization or recomputation
of an encoding for each tile. Sparse unions and trie lookup must not reserve or
scan the exponential key universe. Enumeration must charge failed branches as
well as outputs. Word-width proofs must cover arithmetic intermediates, not only
final values. The fast multiplication bodies remain paper definitions assembled
from this vocabulary; correctness of an ordinary slow algorithm is not evidence
for the fast complexity claim.

Run the full library build/test suite, computation seal audit, axiom audit and
whitespace check. Keep `Charged.lean`'s working-tree/HEAD hash equal. Independently
check concrete execution examples against exact vectors and memory growth.
Review the final staged diff and record the exact verified commit. Report any
remaining unsupported operation precisely rather than declaring the complete
paper ready from a partial API.

## Progress

The plan was recorded before implementation. The implementation establishes the
minimal charged authoring basis, with checked reusable operations, rather than
turning each paper procedure into a new library opcode. Word arithmetic,
represented storage, branches and mutable sealed-index loops suffice to write
finite strings, node pools, tries, coefficient arithmetic and recursive work
stacks without observing machine words for free. Higher-level optimized
algorithms still need source bodies and their own invariants and complexity
proofs. Providing this basis is distinct from claiming that those bodies exist.

### Implemented authoring basis

- `ChargedWord` in `Machine.lean` provides literals, wrapping arithmetic,
  division/remainder, comparisons, high multiplication, bitwise operations,
  variable shifts and leading-zero count over the existing sealed `Word w`.
  It uses the RAM `Op` vocabulary and arbitrary source space parameter. Existing
  `Charged StdOp Cell` clients remain valid; these additions do not convert a
  `StdImpl` price into an implementation.
- `ChargedVector` seals contents and stores its length as a word. Allocation,
  read and write have exact RAM certificates in `ChargedStorage.lean`. Bounded
  mathematical input lists have representation witnesses; runtime construction
  pays allocation and stores. Source writes return new snapshots.
- `ExactRealizes` relates different source/concrete result types through the
  updated memory and proves equality of every opcode count. Bind, consequence,
  branch, arbitrary-price transfer and conversion to `Realizes` are proved.
- `ChargedLoop` supplies source loops with sealed indices. Its generic exact
  rule supports different mutable accumulator types. A stopping body retains
  the old accumulators in the updated memory, so its postcondition must show
  that their relation still holds there. Exhaustion also pays a guard. `forWord` supplies static word-universe fuel
  without observing the runtime count, and its sharp cost bound depends on the
  represented length, not on that large fuel allowance.
- `ChargedView` shares backing storage with word offset, stride and length;
  reads and writes prove all indexing intermediates and physical address bounds.
  `ChargedVector.fill` and `copy` prove current-version representation;
  copying also proves preservation of a disjoint read-only source.
- `ChargedRecord`, `ChargedSignedStorage` and `ChargedSigned` expose record
  allocation/read/write, signed storage and signed arithmetic through Charged.
  Records use disjoint fields and physical allocation is proved separately from
  logical source profiles. Both signs of zero remain admissible.
- `ChargedString.equalPrefix` charges reads and comparisons and has exact
  realization, a linear control-inclusive bound and a general mathematical
  prefix theorem with explicit complete-fuel and word-width premises.
  `prefixForWord` supplies complete fuel without decoding the count, so only its
  word-width and represented-input premises remain.
- `ChargedArithmetic.ceilDiv` avoids forming `n+d-1`. The positive-divisor
  correctness proof derives that its final increment fits from the input width.
  `ChargedModular` exposes canonical signed residues, overflow-avoiding reduced
  addition, bounded-product multiplication and signed-zero testing, with exact
  realization and mathematical specifications.

### Costs checked from programs

| Operation | Unit RAM cost, including internal arithmetic/control |
| --- | --- |
| Word literal/arithmetic/comparison/bit operation | 1 |
| Vector allocation of n cells | n |
| Vector indexed read or write | 2 |
| Indexed view read or write | 4 |
| Two-field record allocation | 2n |
| Record read or write | 4 |
| Signed storage read / write | 6 / 5 |
| Signed magnitude add | 1 for equal signs, 2 for opposite signs |
| Canonical signed residue | 1 for positive sign, 3 for negative divisible input, 4 otherwise |
| Reduced modular add / fitting-product multiply | 3 / 2 |
| Ceiling division | 4 for exact division, 6 otherwise |
| Dynamic word iteration, body cost at most B | at most 3 + stored limit * (B+2) |
| Initialized fill | at most 3 + 4 * fuel |
| Initialized disjoint copy | at most 3 + 6 * fuel |
| Initialized prefix comparison | at most 3 + 7 * fuel |
| Complete dynamic fill / copy / prefix | at most 3 + 4n / 3 + 6n / 3 + 7n |

These bounds include the final guard, guards on exhausted fuel, and increments
on continuing bodies. In prefix comparison a mismatch is stored as a false
accumulator; the next guard is paid before its early exit. A first-symbol
mismatch therefore costs 10, not 9. No later symbols are read. A zero-fuel
comparison costs 3 and returns true for its empty visited prefix; the general
prefix correctness theorem requires fuel covering the requested length.

The proof-side vector contents are a logical model, not a statement about the
running time of a native Lean List backend. The concrete RAM certificates are
the evidence for the machine claim. Neutral source residency profiles do not
supply physical-memory bounds. The general fill/read regression separately
proves that physical size grows by exactly the allocated length, even under
truncated execution.

### What an exact certificate does not check

Equality of opcode tallies is a semantic theorem about the supplied RAM model;
it is not an automatic check of admissible program syntax, uniform input
access, native Lean execution time or fidelity to the paper. Arbitrary pure
Lean computation over unsealed inputs can evade a tally in both source and
counterpart. The supplied implementations use primitives with forwarding and
bounded control; their reviewed bodies and represented-input boundaries are
part of the evidence. A client must retain that discipline when composing them.
[Program-Language.md](Program-Language.md) records the broader grammar gap;
`lower_num%` only checks its registered fragment. The seal and axiom audits alone
do not close this gap or establish a whole-paper runtime claim.

### Algorithm-specific work still needed

The implementation does not claim completion of the entire numbered convenience
library sequence. Complete reusable sparse trie insertion/deduplication,
incremental subset/box enumeration, source square-root/power/prime algorithms,
cyclic convolution and explicit recursive stacks remain follow-up modules.
They are expressible with the new charged vocabulary; a missing optimized body
cannot be replaced by an invented primitive, a generic dictionary price or a
brute-force algorithm under a fast cost contract. In particular a bounded
alphabet trie should reserve O(alphabet size * node capacity) storage and charge
per visited edge, rather than reserving the exponential key universe. Recursive
encodings must retain sharing across tiles and charge actual scratch allocation.

The 3sum project's solver, prime-count multiplication and preprocessing bodies
remain project proof/implementation obligations. This work neither changes its
pins nor reclassifies same-paper results as borrowed assumptions. Updated
extension guidance points authors to installed APIs and keeps such requests
visible for repair and human inspection; no completion gate is added.

### Review and regression evidence

The author reviewed the primitive bodies against their RAM counterparts and
checked branch-dependent vectors, bounds, state threading, stale snapshots,
disjoint fields, input witness satisfiability, exhausted fuel, early exit,
allocation frontiers and intermediate wrapping. This batch was reviewed by the
integrating author and Lean's kernel; it is not described as an additional
independent-agent review.

`ArlibTest/Computation/ChargedAuthoring.lean` contains concrete and general
regressions. A source allocation/fill/read returns 7, allocates three cells and
costs 23 with the vector lit=5, alloc=3, lt=4, add=7, store=3, load=1. Its
parameterized exact theorem applies to arbitrary widths, admissible initial
memories and instruction prices, including incomplete fuel. Disjoint copying
costs 28 and grows an encoded three-cell input to six cells. Signed storage
roundtrip returns -3, allocates four cells and costs 18. Shared strided views
read without materialization and cost four. Tests also cover high multiplication,
word wrapping, negative residues, modular sum overflow avoidance, empty-width
loops, and rejected cell projection, pattern elimination and free word equality.

Final full-build, test, audit and commit results are recorded below.


### Final verification (2026-10-07)

- `lake build`: passed, 3530 jobs.
- `lake test`: passed, 3770 jobs. The authoring test file contains 61 example
  declarations, three named general theorems and four rejected seal breaches.
  The only warning is the existing `ArlibTest/Computation.lean:497` lint warning.
- `lake env lean scripts/ComputationAudit.lean`: passed, 2047 declarations; no
  eliminator leak, unapproved noncomputable definition or foreign private constant.
- `lake env lean scripts/AxiomAudit.lean`: passed, 11027 declarations; only
  `Quot.sound`, `Classical.choice` and `propext`.
- `Charged.lean` working-tree/HEAD Git blob hashes both
  `f54da0d3ea009251931ed77251e5276affe0bd8d`; no change to its implementation or
  public interface.
- Staged review found one trailing space in the previously untracked modular
  module. It was corrected before commit; no semantic change was made.
- Tex2Lean TypeScript check passed. Current writer/surface checks passed 72/72
  and report-feedback checks passed 21/21. Guidance changes remain in Tex2Lean's
  working tree, outside this Arlib commit. No dependency pins were changed.

The Arlib commit includes the previously developed, verified realization/storage
modules on which this authoring layer depends, together with their tests and
review documentation. Unrelated `.claude/` and `writeup/` work is not included.
The new authoring batch uses manual sources and kernel-checked tests; it does not
claim a new external live-writer evaluation beyond the earlier recorded tests.
