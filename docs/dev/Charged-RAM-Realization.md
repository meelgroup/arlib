# Charged programs with certified RAM realizations

Status: foundation and follow-up implementation independently reviewed on 2026-10-06. Verification records distinguish the initial milestone from the follow-up modules.

## Requirement and scope

Keep every existing public Charged type, constructor interface, combinator, signature, and accounting semantics. Existing author-written algorithms keep returning Charged. Add executable RAM counterparts and kernel-checked relational certificates in separate modules. Do not add implementation fields to Charged, alter its monad, silently reprice its tally, or require algorithms to use another monad.

The first complete milestone is the additive realization framework, bounded numeric implementations, sealed indexed buffers, charged word-counter loops, and a fully proved early-exit buffer scan. It establishes the architecture with actual RAM programs. It does not assert that all eight standard carriers, randomized operations, arbitrary real arithmetic, or the 3sum fast solvers have already been implemented. Those extensions use the same certificates; their prices remain conditional until concrete code is proved.

## Why there is no function compile : Charged ... -> RAM ...

Charged has already evaluated its program and retains its value, commutative tally and space profile. It loses instruction order, arguments and control flow. Recovering a program from those fields is impossible in general. Arbitrary Lean pure expressions also need not be machine operations. Keep the source program and associate a separately composable realization with it. The restricted lower_num% frontend now constructs RAM counterparts from supported source definitions, and ram_refine applies proved witness-construction rules. Broader lowering registrations remain future work, without changing the Charged interface.

The foundation uses a shallow relational framework and explicit certified combinators. The added frontend generates code separately from kernel-checked realization certificates; translation success alone is not proof of correctness. It follows the existing Program-Language.md distinction between executable operations and specification observations. No namespace-wide exemption or certificate grants permission to compute arbitrary mathematical functions for free.

## Semantic contract

Define Realizes p q Pre Post budget, where p is the unchanged Charged computation, q its RAM program, Pre constrains the initial machine state, and Post relates p.val to q.val and the final state. The certificate proves Post and RAM unit steps <= budget for every state satisfying Pre. Post is state-indexed, so containers can be related to memory. An optional state/footprint invariant is carried in Post; memory preservation must be proved, not inferred from equal output values.

Compositional rules cover pure forwarding, bind, Boolean branch, read-only word-loop iteration, and mutable loops with different abstract/concrete accumulators and state-indexed relational invariants. The bind rule requires the first postcondition to establish the continuation precondition, and charges the sum of the component budgets. Preconditions cannot be treated as evidence of an input encoder: concrete examples must exhibit admissible encodings. A false precondition makes a conditional theorem vacuous and must not be marketed as implementation existence.

Generic certificates state soundness inside Arlib's RAM semantics. They do not certify host Lean wall-clock execution or automatically validate every RAM definition against the program grammar. Concrete library implementations use sealed words, real primitives and bounded library loops. No admitted proofs or new axioms are acceptable.

## Pricing connection

StdImpl stays unchanged as a size-dependent pricing table. A certified standard-operation contract couples concrete code and representation correctness with actual RAM steps <= I.bound opcode currentSize. Monotonicity derives the ceiling at maximum size. This does not imply exact equality with CostVec.exchange: bound_ok only bounds the advertised rate, and both actual code and that rate may be below a larger bound. Prove a whole-program bound from the realized operations plus explicit loop/setup/boundary overhead.

The current abstract pure-body loop can have zero tally. Therefore never state RAM steps <= ceiling * Charged.steps without either additional control budget or a premise ensuring that abstract accounting pays for the control. Preserve old theorems and add an explicitly named bound including overhead.

## Concrete representations

Numbers: relate Num Nat to a Word through specification-only Num.get and Word.toNat. Literal, addition, multiplication and comparison receive RAM counterparts. Unbounded arithmetic requires operation-specific no-overflow conditions; do not truncate silently. Signed integers now use the explicit sign/magnitude implementation described below. Real ceil remains unsupported machine arithmetic, not an assumed one-word operation.

Buffers: a private runtime representation holds Word base and Word length, with a noncomputable mathematical view for specifications. The block represents a List Nat via HoldsList, and its stored length equals list length. Read/write compute addresses through RAM add/load/store. A handle can refer to existing input memory; allocation is a separate charged operation. Empty buffers, frontier overflow, out-of-range indices and aliasing must have explicit semantics. Update proofs preserve unrelated blocks and keep length fixed. Buffer metadata forwarded in registers does not claim it was read from memory.

Loops: an additive word-counter loop charges literal initialization, a guard per visited position, and increments only when continuing. A proof-only structural bound ensures termination; executable data and stopping decisions use words and charged primitives. Early exit does not execute remaining bodies. Existing iterate remains compatible. Streaming implementations of abstract range loops are a separate optional optimization and must preserve existing value/tally/profile theorems.

## First end-to-end algorithm

Write a Charged scan which reads each represented element and compares it to a target, stopping on a match. Its RAM counterpart uses the sealed buffer and word-counter loop. Prove output equivalence for all bounded represented lists, unchanged memory, a worst-case linear bound including guard/address/load/comparison/increment costs, and concrete tests distinguishing early exit from full traversal. Also show an empty-body machine loop incurs positive control work.

## Modules and verification

- Realization.lean: relational certificate and sequencing/selection rules.
- StdRealization.lean: certified standard-operation bounds and maximum-size ceiling transfer.
- Realization/Loop.lean: read-only loop realization with explicit control budget.
- Realization/Num.lean: existing Num operations implemented by RAM words.
- Buffer.lean: sealed handles, indexed operations, representation and frame proofs.
- WordLoop.lean: charged loops, invariants and cost rules.
- Realization/Scan.lean: unchanged Charged source, RAM counterpart, all-input theorem.
- ArlibTest/Computation/Realization.lean: execution checks, public API examples, wraparound and negative/early-exit cases.

Integrate additive imports into Computation and ArlibTest. Update audit specification allowlists only for exact new specification names. Run targeted builds, existing computation smoke tests, full lake build/test, computation audit and axiom audit. Review final proofs independently for missing bounds, vacuous conditions, hidden arithmetic, claims stronger than model semantics and Charged interface changes. Preserve preexisting work and all attempted changes.

## Follow-up sequence

The follow-up implementation retains the top-level Charged interface and adds the concrete components below. These are specific implementations and proof rules; they do not assert that every existing carrier operation, arbitrary source program, or paper subroutine has a RAM implementation.

| Milestone | Implementation | Certified scope and bounds |
| --- | --- | --- |
| Mutable composition | `Realization/MutableLoop.lean` | Different abstract/concrete accumulator types; representation transported through the actual updated state; guarded body bounds; stop invariant; `3 + fuel * (bodyBound + 2)` including control. |
| Stateful storage | `RAMRoster.lean`, `RAMDict.lean`, `RAMQueue.lean` | Stored metadata; actual reads/writes; all-input correctness for the supplied operations; disjoint frame conditions; charged initialization. Direct-address roster/dictionary require bounded natural keys; queue requires unused tail capacity. |
| Certified pricing | `CertifiedStd.lean`, `DirectAddressStd.lean` | Actual charged opcode, representation relation and concrete cost tied to a monotone size-dependent StdImpl bound. A table alone cannot supply a missing implementation. |
| Matrices | `Matrix.lean` | Row-major dimensions stored as words; product/intermediate/index/address bounds; valid read/write cost 4; checked access pays comparisons and costs at most 6; allocation/initialization scales with cell count. |
| Signed arithmetic | `SignedWord.lean`, `Realization/Signed.lean` | Sign plus bounded magnitude representation; all sign cases and zero; actual word operations; explicit no-overflow premises; implementations of existing Num Int operations. |
| Probabilistic refinement | `ProbRAM.lean`, `Realization/Probability.lean` | Joint result/state/cost distributions, independent fair-bit intrinsic, support-wise cost/invariant bounds, state-aware output decoding, bind and deterministic lifting. |
| Source lowering | `Lowering.lean` | `lower_num%` translates supported existing Charged definitions; `ram_refine` applies kernel-checked realization rules and leaves genuine side conditions. |
| Writer migration | Tex2Lean surface preparation, Program, extension and coordinated repair prompts | Inspect installed capabilities, compose concrete implementations, preserve unresolved contracts/reports, include control/storage/boundary costs, and distinguish seal acceptance from realization. No new approval/completion gate. |

### Representation and storage decisions

Roster and dictionary use bounded direct addressing, not a balanced tree or a hash table. A key universe of capacity U reserves U occupancy cells, and the dictionary additionally reserves U value cells. Live cardinality can be much smaller. Runtime access is constant in cardinality, but initialization and physical storage depend on U. A paper whose bounds require storage proportional to live size needs a different implementation and must retain that dependency as an explicit gap.

Queue storage advances a head word and retains the allocated region. Dequeue does not reclaim or reuse the consumed prefix. Enqueue therefore requires `head + liveLength < capacity`; merely having `liveLength < capacity` is insufficient. A circular queue with prefix reuse is a separate implementation.

The concrete operation ceilings are roster membership 4, insertion 8, erasure 9; dictionary lookup 6, insertion 10, erasure 9; queue enqueue 5, dequeue 7 and emptiness 2. Roster/dictionary cardinality equality costs 1 and stored size forwarding costs 0. StdImpl requires positive operation bounds, so the size operation's price is conservatively 1. Every supplied operation has an opcode-specific CertifiedStdOperation; other pricing-table entries remain uncertified. These direct-address access bounds do not grow with live size. Initialization costs U + 1 for roster/queue and 2U + 1 for dictionary, excluding literals used to obtain the capacity. Physical allocation adds U or 2U cells, and updates preserve the actual state size.

Metadata and signed values occupy a fixed number of word/Boolean registers. The RAM model prices declared numeric and memory primitives, while forwarding registers and branching on already obtained Booleans are free. This is the existing model convention, not a claim about host-language runtime or hardware instruction costs.

Frame predicates prove preservation of explicitly disjoint regions. They are ownership premises for the certified call, not a linear type system that forbids constructing aliases. Stale handles must not be treated as the current representation after a mutation.

### Probabilistic boundary

ProbRAM is the mathematical semantics of a stochastic RAM with an independent fair-bit intrinsic. Exact PMFs and their sequencing are noncomputable. Deterministic programs still use executable RAM code; stochastic driver definitions do not constitute a native entropy source or a deterministic PRNG implementation. A physical random source or a tape implementation requires its own contract. The audit permits only the exact reviewed driver constructors, separately from specification observers; arbitrary downstream noncomputable programs remain rejected.

Probability certificates compare the actual decoded output distribution with the abstract law, preserve invariants on every reachable execution, and bound costs on the execution support. Decoders can inspect the final state in the specification, so a program returning a handle can represent a mutable mathematical result. Independent draws and duplicated uses of one draw are distinguished in regression proofs.

### Lowering and adoption boundary

The supported initial lowering fragment covers Num Nat static literals/add/mul/comparison, forwarding values, do/bind/pure, Boolean branches, products, supported nonrecursive procedure calls and source functions with represented arguments. It checks canonical natural numeral/arithmetic/order instances; a custom instance cannot silently change the meaning of the generated operation. Compile-time unfolding may specialize away unused helper arguments. Runtime native computation, raw charged operations without registered implementations, opaque procedures and recursion are rejected.

Lowering emits code, not an automatic correctness or complexity theorem. `ram_refine` uses registered proved rules; representation, overflow, intermediate-state and budget goals remain explicit. Container, loop, signed and probabilistic code currently compose through their public APIs and certificates rather than this restricted lowering frontend. Adding registrations for those constructs is subsequent frontend work, not an assumption that their implementations are missing.

Existing model writers must check the installed Arlib version. The new source is local development work; an older dependency pin does not acquire these APIs through a prompt. Writer guidance does not silently upgrade pins or pretend absent declarations exist. The old 3sum fixture remains an independent formalization; these reusable modules do not by themselves close its missing solver, parameter or full word-RAM proof obligations.

Remaining broader work includes live-size storage implementations when universe-sized direct addressing is unsuitable; circular queue reuse; more carrier operations and lowering registrations; automatic physical-space certificates across arbitrary Charged profiles; and complete paper-specific migrations. No universal lowering or whole-library pricing certification is claimed.

## Review record

Three independent reviewers examined the architecture and concrete implementations. The architecture reviewer implemented the core, while buffer and word-loop reviewers independently checked those certificates; the scan was reviewed by all three. Findings and resolutions:

- Charged must retain its public interface and accounting semantics: its source file is unchanged.
- Bind must transport intermediate representation facts in the updated state: the compositional rule does this, and the public test exercises it.
- Actual cost cannot be inferred from a pricing formula alone: StdRealizes requires a concrete certificate, and the whole-program transfer includes explicit overhead.
- Unsatisfiable preconditions do not establish implementation existence: Buffer.encoded_holds proves admissible encodings for every bounded list.
- Loop fuel could truncate traversal: the full scan certificate requires fuel equal to represented length, and adversarial tests demonstrate shorter fuel misses a late match.
- Empty-body loops must pay control costs: exact execution tests demonstrate this.
- Abstract fold stopping semantics retains the prior accumulator on none: the scan records a match with some true, then stops on the next body call without another read. That entails one additional increment and guard after an early match, and the cost tests include it.
- Generic loop claims were too broad for the initial scan-specific proof: Realization/Loop now provides a separate read-only realization rule; general mutable relational loop composition is now supplied by Realization/MutableLoop.
- Certificates do not enforce the complete source grammar or compile arbitrary pure Lean computations: this remains a stated limitation, with automatic source lowering limited to the registered numeric fragment.

No correctness blocker remained in the implemented scope. All implementation proofs are kernel-checked; no new axioms or admitted proofs are introduced. Final numeric pricing corollaries and the read-only loop rule also received an independent review after integration.

## Initial milestone verification results

- `lake build`: passed, 3503 jobs.
- `lake test`: passed, 3203 jobs, including 44 new public API examples. One existing lint warning in ArlibTest/Computation.lean was replayed; the new modules and test file have no warnings.
- `lake env lean scripts/ComputationAudit.lean`: passed, 1230 declarations; no eliminator leak, noncomputable program, or borrowed private constant.
- `lake env lean scripts/AxiomAudit.lean`: passed, 10112 Arlib declarations; only Quot.sound, Classical.choice and propext.
- `git diff --check`: passed.
- `git diff -- Arlib/Computation/Charged.lean`: empty. Neither its public interface nor implementation was changed.

Regression examples include intermediate representations in bind, concrete Std ceiling transfer, admissible input encodings, allocation, indexed writes and disjoint frames, actual wrapping arithmetic with a rejected natural-number overflow premise, zero-cost abstract bodies with positive RAM control cost, empty and one-bit scans, early/late/missing matches, and deliberately insufficient fuel.

## Using the implementation

Existing algorithms continue to have type `Charged κ κₛ α` and use their existing do notation. Define a RAM counterpart using the sealed primitives and library combinators; certify each operation with NumRealization, Buffer specifications, or another proved implementation. Compose certificates with Realizes.bind and the branch/read-only-loop rules. Add representation, word-width and memory preservation obligations to the pre/postconditions.

For the concrete worked example, `ScanRealization.scan` is the abstract source, `scanRAM` is its executable RAM counterpart, and `realizes` packages output agreement, input preservation and the bound `3 + 5 * fuel`. Its input precondition requires fuel equal to represented length. `Buffer.encoded_holds` supplies a representation existence theorem for bounded lists; it does not charge input construction because it specifies the initial input boundary. Runtime construction uses `Buffer.allocate` and charged writes.

The certificates supply actual programs and checked bounds but do not automatically extract code from an arbitrary evaluated Charged value. They also do not yet turn a Charged Profile into a general physical-memory bound; the buffer predicates supply concrete bounds for this milestone.


## Follow-up review record

The follow-up modules were reviewed independently across the same three implementation/review agents and the integrating author. Mutable loop review checked stopping semantics, updated-state invariants, different accumulator types, fuel coverage and no-wrap counter arithmetic. Matrix review checked both multiplication intermediates and physical address bounds. Signed review checked negative zero, all sign combinations and overflow premises. Container review checked occupancy/value separation, exact live counts, disjoint frames, stale slots and reserved capacity.

A lowering review found that matching operation names alone could discard custom Lean typeclass instances. The generator now validates canonical OfNat/Add/Mul/LE and comparison-decision instances; negative tests cover misleading alternatives. Code generation remains separate from kernel-checked realization.

Probabilistic review required a state-aware decoder instead of a decoder of the returned value alone. The corrected certificate decodes the joint returned value/final state; a random mutation example proves the law, preserved neighboring memory and actual cost through compositional rules.

The audit's noncomputable allowances distinguish exact specification names from exact stochastic semantic constructors. No namespace-wide exemption is introduced. Charged.lean remains unchanged.


## Follow-up verification results

- `lake build`: passed, 3515 jobs.
- `lake test`: passed, 3224 jobs. Follow-up modules add 205 kernel-checked examples, including 10 rejected lowering cases; the original 44 realization examples also remain passing. Only the existing ArlibTest/Computation.lean lint warning was replayed.
- Computation audit: passed, 1585 declarations; no eliminator leak, unapproved noncomputable definition or foreign private constant.
- Axiom audit: passed, 10496 declarations; only Quot.sound, Classical.choice and propext.
- Charged.lean: working-tree and HEAD Git content hashes both f54da0d3ea009251931ed77251e5276affe0bd8d. Its interface and implementation are unchanged.
- Arlib and Tex2Lean `git diff --check`: passed.
- Tex2Lean TypeScript check: passed. Writer/surface tests 70/70, denotation tests 106/106, pipeline tests 181/181, report-feedback tests 21/21, model-repair tests 15/15 and model-feedback tests 6/6 passed.

The prepared live CLI test was authorized and run on 2026-10-07 in `/private/tmp/arlib-ram-milestones-live-20261006`. The earlier automatic-review rejection concerned additional private Arlib source access; the user subsequently explicitly approved that access and the prepared test. An interruption preserved the generated source and diagnostic logs; the same CLI session resumed and completed.

### Live test results

- **Numeric composition:** unchanged Charged source with literals 3 and 5, charged comparison, addition/multiplication branches; `lower_num%` generates the RAM counterpart. A theorem identifies the generated code with both branches present. Selection returns 8 in exactly 4 unit RAM steps for every initial state, preserves memory, and has a Realizes certificate. Both arithmetic alternatives also have general represented-input certificates under explicit no-overflow premises, using ram_refine.
- **Concrete storage:** a RAM 8 program allocates a 2 by 3 matrix, explicitly stores initial entries 1 through 6, writes 9 at (1,2), and reads that entry. It returns 9, reserves 6 cells, and costs exactly 46 steps: 19 literals, 6 allocation charges, 3 multiplications, 10 additions, 7 stores and 1 load. Representation before/after update, allocation/address bounds, physical growth and disjoint frame preservation are proved.
- **General input boundary:** valid matrix reads are proved for every width, represented matrix and bounded row/column pair, with unchanged state, cost 4 and a nonwrapping address. Every bounded rectangular list has a represented-input witness. These specification encodings are not free runtime construction.
- **Independent checks:** Program.lean, Live.lean and the integrating author's Verify.lean all elaborate successfully. Executable definitions are computable and contain no direct Word.toNat/Charged.val/Num.get observations. Checked certificate axioms are only propext, Classical.choice and Quot.sound; no sorry, added axiom or unsafe/native proof shortcut appears in the generated implementation/proof source.
- **Structured reporting:** the initial standalone prompt specified array names but omitted the detailed production report contract. The writer initially used prose where declaration names and structured objects were required. The actual extension parser rejected that report. A follow-up supplied the production contract; the corrected report is accepted and lists 24 proved declarations, with no open declarations or semantic/dependency requests for this focused test. Source hashes prove the verified Lean files did not change during report correction. Original malformed reports and every failed attempt remain preserved.

The live proof attempts exposed an absent tactic import, simplification mismatch and heartbeat-heavy conversion. The writer resolved them with the required tactic import and explicit literal-value/list-update rewrites, without changing Arlib. Historical failures are retained rather than described as passing snapshots.

Artifacts: `writer.prompt.md`, `resume.prompt.md`, `report-correction.prompt.md`; executable `Program.lean`; proof-side `Live.lean`; `Inspection.lean` and `Verify.lean`; original/corrected structured reports; `evaluation.result.json`; original/resumed/report CLI logs; and `attempts/` source snapshots and diagnostics.

This focused live result verifies the tested numeric and matrix capabilities. It does not establish the complete 3sum implementation, general lowering, missing fast solver bodies or whole-paper word-RAM complexity. No dependency pins or original paper-project files were changed.

## Reduction storage: modular arithmetic, signed buffers and pooled buckets

The next implementation batch supplies the reduction's arithmetic and storage
building blocks, while leaving `Charged.lean` unchanged. All executable definitions
use existing RAM instructions. The added modules are exported by
`Arlib.Computation`.

| API | Representation and proved behavior | Unit-cost RAM bound |
| --- | --- | --- |
| `NumRealization.division`, `remainder` | Existing sealed `Num Nat` values; division and remainder agree with mathematical natural arithmetic. The remainder source composes existing division, multiplication and subtraction operations. | 1 each |
| `Modular.signedResidue` | Canonical nonnegative residue of a sign/magnitude integer under an explicitly positive word modulus, including negative multiples and negative zero. | At most 4 |
| `Modular.add` / `realizes_add` | Addition of reduced residues. Subtract the second residue from the modulus and compare before choosing addition or subtraction; the possibly overflowing sum is never formed. | 3 |
| `Modular.mul` | Product followed by remainder, with an explicit premise that the product fits in the word. | 2 |
| `RecordBuffer` | Two disjoint buffers store two-word records. `Holds`, reads, updates, allocation and disjoint frames are proved. Stored capacity is a forwarded word register. | Read/write 4; allocation `2*M` |
| `SignedBuffer` | Two cells per integer: sign code 0/1 and unsigned magnitude. Reads reconstruct the sign through a charged comparison; writes materialize its code with a charged literal. Both signs of zero are allowed. | Read 6; write 5; allocation `2*M` |
| `BucketBuffer` | Shared record/link pool plus bucket heads; occupied count and capacity are word registers. One-based pointers use zero for an empty chain. | Allocation `3*M+p+1`; successful push 14; head read 2; node read at most 10 |
| `WitnessScan` | Candidate records contain two indices into signed edge-weight buffers. Load both weights, add the fixed third weight, and test the exact signed sum. | Candidate check at most 18; complete traversal bound `2+28*fuel` |

`BucketBuffer.Holds` describes physical storage, bounded pointers and disjoint
fields. A bounded pointer graph can still contain cycles: `Chain` specifies a
finite sequence and `Models` ties every logical bucket to such a sequence.
`allocate_models` establishes empty buckets; `push_models` proves exact prepend
behavior for the selected bucket and preservation of every other bucket.
`Chain.setFresh` and `Chain.prepend` provide the corresponding local rules.

The pool reserves `3*M+p` cells in total, rather than `M*p` cells. Used slots are
monotone and there is no reclamation or resizing in this API. Insertion reverses
insertion order; an algorithm requiring a particular order must account for that
explicitly. Invalid keys and full capacity return `none` and preserve memory.
Pointer traversal pays for its zero comparison, loads and address arithmetic;
it does not construct a `List.range`. Structural fuel bounds traversal, and
completeness requires the represented finite chain's length to fit in that fuel.
Even exhaustion at zero fuel executes the final pointer comparison. A too-short
scan has defined behavior but cannot satisfy the completeness premise.

`WitnessScan.source` uses the existing `Charged` interface. `WitnessScan.realizes`
relates that source to executable traversal and exact checks, preserving both
signed inputs and the pool. Its precondition explicitly requires finite chain
representation, valid indices for every occupied record, intermediate magnitude
bounds, represented base weight and sufficient fuel. The source's Boolean result
is proved equal to `List.any` of the exact three-term zero-sum predicate. A modular
collision does not prove that predicate.

The signed storage is sign/magnitude, not a single-word two's-complement encoding.
Its flags also need a representable one (`1 < 2^w`). Modular multiplication still
has a product-width obligation; there is no claim of a full-width multiplier.
Allocation requires valid intermediate frontiers and sufficient address space,
including empty allocations. Initial mathematical representations are proof
vocabulary; runtime construction pays through allocation and stores.

The extension's preparation, program, extension and repair guidance now names
these installed-library capabilities and the ordering, capacity, fuel and
arithmetic obligations. It still requires inspecting the installed version and
preserving semantic/dependency reports; no gate or automatic dependency upgrade
was added. Numeric lowering remains limited to its existing registered fragment.

### Reduction-storage verification

- `lake build`: passed, 3520 jobs.
- `lake test`: passed, 3230 jobs. The new test module adds 51 kernel-checked examples
  and 3 rejected seal-breach cases. Only the existing `ArlibTest/Computation.lean`
  lint warning was replayed; the new modules have no warnings.
- Computation audit: passed, 1783 declarations. The only added specification
  exemption is the exact name `RecordBuffer.capacityNat`.
- Axiom audit: passed, 10713 Arlib declarations; only `Quot.sound`,
  `Classical.choice` and `propext`.
- `Charged.lean` working-tree and HEAD hashes remain
  `f54da0d3ea009251931ed77251e5276affe0bd8d`.
- Tex2Lean TypeScript check, 70 writer/surface checks and 21 report-feedback checks
  passed. Both repositories' whitespace checks pass.

Regression cases cover negative residues, negative zero, modulus one, positive
modulus obligations, a modular sum whose unreduced value would overflow, rejected
product-width premises, signed updates and allocation, shared-pool insertion,
invalid keys, exhausted capacity, empty chains, early/late/missing witnesses and
insufficient fuel. The scan certificate is instantiated on a nonempty represented
state, rather than verified only under an empty precondition. Physical pool
updates and finite-chain preservation are separately proved.

### Reduction-storage live writer test

The authorized installed CLI was tested with the updated production writer
guidance in `/private/tmp/arlib-reduction-storage-live-20261007-013556`. Its
computable `Program.lean` allocates and initializes both signed buffers, computes
`-7 mod 5 = 3`, allocates a capacity-two pool with five buckets, inserts two index
records with explicit rejection branches, reads the stored head, and executes the
exact witness scan. All these operations remain in the executable composition.

`Live.lean` proves successful preparation, stored contents and chain order,
capacity exhaustion, disjoint regions, address and intermediate bounds, and
agreement with the retained Charged source. The concrete initialized program
returns true in **138 unit-cost RAM steps**, using **19 physical cells**. Preparation
costs 84 steps and the late-hit scan costs 54. Fuel one returns false in the same
initialized state, costing 28 scan steps and 112 total steps. The proof also gives
primitive cost vectors and an all-width canonical-residue theorem with an
explicit positive-modulus premise. Its general scan theorem retains the actual
representation, index, arithmetic and fuel obligations; the initialized execution
discharges those obligations.

Independent compilation of `Program.lean`, `Live.lean` and the integrating author's
`Verify.lean` passed against the installed library, with installed paths before
any temporary artifacts. Verification checked four executable definitions and
65 live declarations: computable executable bodies, no direct mathematical or
cost observations, no foreign private constants, and only the permitted logical
axioms. Source hashes and independent diagnostics are stored in
`independent.result.json`; `evaluation.result.json` records the focused result.

The first attempt coincided with the integrating author's final bucket-invariant
rebuild and failed while its dependency artifact was unavailable. The writer
preserved that source and diagnostics, detected the repaired installed artifact,
and completed the same session. Other preserved attempts include a reserved-token
name, temporary path shadowing, reversed disjointness proofs and dependent-index
proof tactics. The author's independent verification script also required an
explicit `Nat` annotation for its counter; its failed version is retained. Failed
snapshots are not counted as successful tests. Original source projects and
dependency pins were not changed.

This test establishes these composed library operations on represented inputs.
The key-generation example exercises canonical routing; it does not prove the
paper's complete partition construction or its matrix/Lop solver implementations.
Those remain separate obligations in a complete 3sum paper transcription.


## Charged authoring follow-up

The source-authoring layer now includes sealed charged words/vectors, mutable
word-counter loops, shared indexed views, disjoint bulk copy, record/signed
storage, string prefix comparison, ceiling division and modular operations.
`ExactRealizes` proves equality of the full opcode tally under current memory
representations; costs therefore transfer under arbitrary instruction prices.
`Charged.lean` remains unchanged. The design, cost table, kernel regressions and
precise remaining algorithm-specific milestones are in
[Charged-Algorithm-Authoring.md](Charged-Algorithm-Authoring.md). This authoring
basis is not evidence that the paper's fast solver bodies have been implemented.
