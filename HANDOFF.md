# Handoff — knowledge-compilation lower bounds & automata

Written 2026-07-23. For the next agent picking up this work. Everything below is
in the working tree of `/Users/kmeel8/research/meelgroup-projects/arlib`,
**uncommitted**. Full library builds green (`lake build` → 2478 modules, 0
errors, 0 `sorry`, 0 custom axioms).

---

## 1. What this work is

Three papers formalized into `arlib` (Lean 4 + Mathlib, both pinned `v4.15.0`):

1. **Göös–Kiefer–Yuan**, *Lower Bounds for Unambiguous Automata via Communication
   Complexity* (ICALP 2022) — `source/kc/goos/`. Landed as a **new area**
   `Arlib/Automata/` (namespace `Arlib.Automata`), per an explicit user request
   that automata live outside `KnowledgeCompilation`.
2. **Razgon**, *On the read-once property of branching programs and CNFs of
   bounded treewidth* — `source/kc/razgon/FBDDJOURN.tex`. Landed under
   `Arlib/KnowledgeCompilation/BranchingPrograms/`. **Complete: all six sections
   + both appendices.**
3. **Oztok–Darwiche**, *On Compiling DNNFs without Determinism* —
   `source/kc/darwiche/draft.tex`. Landed under
   `Arlib/KnowledgeCompilation/Forgetting/`.

The build tool: `lake build <module>` for one module, `lake build` for all.
Mathlib is cached (`.lake/packages`) — do **not** rebuild it from source. A build
may pause on a lock if something else is compiling; wait, retry on lock errors.

---

## 2. Files (all untracked / new unless noted)

**Automata area** (`Arlib/Automata/`, namespace `Arlib.Automata`):
`Basic`, `Simulation`, `DNFtoUFA`, `WordCoding`, `Imported`, `Complement`,
`Union`, `Disjointness`, `ErrorReduction`, plus area root `Arlib/Automata.lean`
and `Arlib/Automata/ROADMAP.md`.

**Razgon** (`Arlib/KnowledgeCompilation/BranchingPrograms/`, namespace
`Arlib.KnowledgeCompilation`): `Basic`, `Covering`, `NROBP`, `TreeProduct`,
`Separation`, `Uniformize`, `Equivalence`, `Asymptotics`, `DecisionDNNF`.

**Oztok–Darwiche** (`Arlib/KnowledgeCompilation/Forgetting/`, namespace
`Arlib.KnowledgeCompilation.Forgetting`): `Basic`, `Treewidth`, `Separation`,
plus area root `Arlib/KnowledgeCompilation/Forgetting.lean`.

**Shared foundation** written by hand before the agents fanned out:
`Arlib/KnowledgeCompilation/Communication/TwoParty.lean` (two-party rectangles /
covers / partitions / nonneg-rank for a bare `F : X → Y → Bool`, needed because
the existing `Communication/Rectangle` fixes a *variable* partition, wrong shape
for automata and for sparse set disjointness).

**Modified (tracked) files:** `Arlib.lean` (added `import Arlib.Automata`; note
`import Arlib.Approximation` was *also* added but that is **not this work** — see
§6), `Arlib/KnowledgeCompilation.lean` (wired in BranchingPrograms + Forgetting +
TwoParty, extended docstring), `README.md`, `Arlib/KnowledgeCompilation/ROADMAP.md`
(new §8 Razgon, §9 Forgetting).

Total new Lean: ~12k lines across ~21 modules.

---

## 3. Headline theorems (all `#print axioms`-clean: only propext/Classical.choice/Quot.sound)

**Automata** (`open Arlib.Automata`):
- `Complement.thm_complement` — UFA whose complement needs a large NFA. Conditional
  on inhabited bundles `Imported.UnambiguousDNFHardCNF` (Balodis et al.) and
  `Imported.NondetLifting` (Göös).
- `Union.thm_union` / `Union.thm_union_of_unionHard` — union of UFAs needs a large
  UFA. Ties to the *pre-existing* `KnowledgeCompilation.UnionDerived.unionHard_of_imports`;
  the connecting side condition is `rfl`.
- `Disjointness.exists_sepFamily` (Razborov covering, **fully proved by counting**),
  `Disjointness.DisjFullRank.choose_le_tpPar` (`thm:separation`; full-rank of the
  k-uniform disjointness matrix imported as inhabited `DisjFullRank`).
- `ErrorReduction.anRank_orExtend_le` — the `1/4` upper-bound half of `thm:error`.

**Razgon** (`open Arlib.KnowledgeCompilation`):
- `Razgon.two_rpow_le_size` — `2^{mw/f(x)} ≤ size` for a **uniform** read-once NROBP;
  `hEngine` discharged. `Razgon.maintheor` — explicit `r`,`p` form.
- `Uniformize.uniformize_two_rpow_le_size` — **the same bound with `Uniform`
  REMOVED**. This is the capstone; `uniformize_exists` turns any read-once NROBP
  uniform at size `(size+2)·((size+2)·(2|V|+1)·(|V|+1)+1)`.
- `Equivalence.exists_traditional_of_nrobp` / `traditional_maintheor` — AROSRN ⟷
  textbook two-leaf NROBP.
- `Asymptotics.dmwtw`, `Asymptotics.maintheor` (`n^{k/c}`), `Asymptotics.separ`.
- `DecisionDNNF.separ2` — FBDD/decision-DNNF separation, conditional on
  `DecisionDNNF.OztokDarwiche` (inhabited; see §5).

**Forgetting** (`open Arlib.KnowledgeCompilation.Forgetting`):
- `forgetNNF_spec` — forgetting a d-DNNF for `g` gives a DNNF for `∃Y.g`, no larger.
- `emf_sauerhoff_gFun` — `f_n` is emf to `g_n` (proved outright).
- `thm_sep` / `cor_forgetting` — conditional on inhabited `SauerhoffdDNNFLowerBound`
  and `GndDNNFUpperBound`.
- `jointreeWidthLe_bvaExpansion` (`thm:width`), `jointreeWidthLe_deltaB_two`.

---

## 4. Conventions every file here obeys (do not break silently)

Read `Arlib/KnowledgeCompilation/ROADMAP.md` §1 in full. In brief:
- **No `sorry`, no `axiom`, no `native_decide`.** A result out of reach becomes a
  named hypothesis or an **inhabited** `structure` bundle (see
  `LowerBounds/Imported.lean` for the pattern + its non-vacuity section). Never an
  axiom. A bundle with unsatisfiable fields makes downstream theorems vacuously
  true while `#print axioms` looks clean — so bundles are always inhabited with a
  minimal witness.
- **Circuits & branching programs are DAGs, never trees; size is a vertex/node
  count.** Node type is `Fin size` with a `child_lt`/`edge_lt` field giving the
  topological order. This is why adding nodes is painful (it changes the type) —
  see §5.
- **Explicit bounds, never `O`/`Ω`.** The one exception: `Asymptotics.lean`, where
  the paper's asymptotic repackaging *is* the content — there, every "sufficiently
  large" step is a named, verified numeric threshold.
- Every declaration gets a docstring; every module a substantial header citing the
  source by line, e.g. ``(paper §4, `source/kc/razgon/FBDDJOURN.tex:651`)``.
- Mathlib v4.15.0 gotchas that bit repeatedly: destructuring `ExistsUnique` needs
  **three** components (`obtain ⟨w, hw, hu⟩`); `omit [Inst] in` goes **before** a
  declaration's docstring, not between docstring and declaration.

---

## 5. OPEN ITEMS — what a next agent should pick up

Ranked. Items 1–2 are the only genuine mathematical gaps; the rest is polish.

### 5.1 `thm:bva` clause (i) — ✅ RESOLVED (`Forgetting/MinDegree.lean`, `jointreeWidthLe_deltaA_ge`; `min-degree ≤ treewidth` via a from-scratch farthest-vertex tree-leaf lemma + leaf-pruning induction). Original note kept below for context.
The **only** place in the whole area that is neither proved nor hypothesized.
In `Forgetting/Treewidth.lean`: the *unbounded* lower bound `treewidth(Δⁿ) ≥ n`.
Blocked on `min-degree ≤ treewidth`, which needs leaf-removal induction, which
needs "a finite tree has a leaf" — Mathlib v4.15 has neither treewidth nor that
lemma. **Right first step: a general `Finset`-level tree-leaf lemma**, reusable and
the actual blocker. Clause (ii) (width-2 jointree) is fully proved. If you cannot
close it, leave it dropped and documented — do **not** paper it with a `sorry`.

### 5.2 `separ2`'s decision-DNNF upper bound is imported, not proved
`DecisionDNNF.separ2` is conditional on the inhabited bundle
`DecisionDNNF.OztokDarwiche` (a CNF of primal treewidth `t` has a decision-DNNF of
size `≤ c·2^t·n`). This is Oztok–Darwiche **CP 2014**, *On compiling CNF into
decision-DNNF* — **a different paper** from the 2017 one in `source/kc/darwiche/`
(that one is *On Compiling DNNFs without Determinism*, now fully formalized in
`Forgetting/` and does **not** contain this bound). The user was told this. **If
the CP 2014 paper appears in `source/kc/`, formalize its Theorem 1 and discharge
the bundle** — that removes the last condition on `separ2`. `TreeProduct.
binTree_pathGraph_bounds` already supplies the treewidth side.

### 5.3 Automata `thm:error` end-to-end, and the optional NFAs (Automata ROADMAP §6)
- `ErrorReduction` gives the generic `1/4` upper bound; instantiating it at §4's
  hard function to state the full `thm:error` gap is a short assembly, not written.
- `lem:separation`'s polynomial-size NFAs for `⟨Disj⟩` and its complement are not
  built — the covering family `Disjointness.exists_sepFamily` (proved) is what they
  consume; only the word-encoding + state-count is missing.
- `cl:or` in its *degree* form belongs on the conical-junta side; only the matrix
  version exists. Same proof.

### 5.4 Backward uniformity transport (Equivalence)
`Uniform` transports AROSRN→traditional forwards but not backwards; nothing
currently consumes it. A third reflection lemma would close it.

### 5.5 Structural cleanup the user floated
- **`Communication/` promotion.** `Arlib.Automata` depends on
  `Arlib.KnowledgeCompilation.Communication`. The clean structure is a
  communication-complexity area both depend on. Pure file move + import updates.

### 5.6 Why node-adding is hard (context for 5.1-adjacent work)
`Uniformize` and `Equivalence` both had to insert nodes into a `Fin size`
topological order. **Do not iterate the paper's per-edge induction** (it re-indexes
`Fin size` every step). Both solved it with a single **fixed arithmetic layout**
(node `u` at `u·(m+1)`, subdivision nodes at computed offsets, `edge_lt` by
`omega`). Reuse that pattern for any further node-surgery.

---

## 6. NOT this work — leave alone / ask before touching

- **`Arlib/Approximation/`** (Coresets, LewisWeights) and **`Arlib/Approximation.lean`**:
  appeared during this session, timestamped, clearly the user's parallel work. It
  is wired into `Arlib.lean` (the `import Arlib.Approximation` line is **not**
  mine). Builds green. Not part of this task — do not modify or attribute.
- **`source/`**: third-party paper sources (arXiv tarballs, PDFs, the three `.tex`
  papers above). Deliberately untracked throughout repo history; docstrings
  reference it by path. Committing third-party PDFs is a licensing call for the
  user, not us.
- **`${env:HOME}/`**: a stray directory in the repo root from an unexpanded shell
  variable, holding a copy of Claude session data. Junk, but holds session data —
  flagged to the user, not deleted.

---

## 7. Git / commit state

- `main` == `origin/main` == `59a5980`, in sync. No unpushed commits.
- **Nothing from this session is committed.** All of §2 is working-tree changes.
- The user has **not** authorized a commit yet — the last explicit instruction was
  "create a handoff". **Do not commit or push without asking.** When you do, note
  that a clean commit should exclude `source/`, `${env:HOME}/`, and `HANDOFF.md`
  itself unless the user says otherwise, and probably should not bundle the
  unrelated `Approximation/` work.

---

## 8. Notable findings recorded in the code (paper errors / deviations)

These are written up in the relevant module docstrings and roadmap §8.4/§9; listed
here so the next agent doesn't rediscover them:
- Razgon `k ≥ 50` is unnecessary (`k ≥ 3` suffices, `b = 32` kept); two of his
  "sufficiently large `r`" steps are vacuous; his `separ` chain loses a factor of
  eight by substituting `r ≥ log n/2` too early.
- `Asymptotics.maintheor`'s constant is `64·f(5)`, not the paper's `32·f(5)` — a
  `Nat.log` rounding artefact; with real logs the paper is correct.
- Razgon's `mincase` "w.l.o.g." (`:855`) is false as written; repaired by counting.
- `dmwtwstruct`'s "w.l.o.g. u₁…u₄ in order" (`:965`) is not a symmetry — it needs a
  median; one of four subtrees is discarded.
- AROSRN→traditional backward direction relies on a sink fact the paper never
  states; the "not constantly false" proviso is unnecessary.
- Göös `lem:UFA-CC` is *not* "proved the same way" as `lem:NFA-CC` — the fixed word
  lengths are what upgrade the cover to a partition. Göös's length-counter product
  step is unnecessary given our `Simulation` only constrains split words.
- decision-DNNF ⊆ d-DNNF needs no decomposability.
- Both `separ`/`separ2` *name* `T_r(P_r)` but *prove* `T_r(P_{2r})`.
