# `Arlib.Automata` — roadmap

Entry point for anyone picking this area up.

**Source.** Mika Göös, Stefan Kiefer, Weiqiang Yuan, *Lower Bounds for
Unambiguous Automata via Communication Complexity*, ICALP 2022, in
`source/kc/goos/`. Section files are `parts/*.tex`; line numbers below refer to
those.

**What the paper proves.** A UFA is an NFA with at most one accepting run per
word. Three blowup theorems:

1. **Complement** (`parts/complementation.tex`) — a language with an `n`-state
   UFA whose complement needs `n^{Ω̃(log n)}` states even as an NFA.
2. **Union** (`parts/union.tex`) — two languages with `n`-state UFAs whose union
   needs `n^{Ω̃(log n)}` states as a UFA. This is the paper's main technical
   contribution.
3. **Separation** (`parts/separation.tex`) — a language `L` with `L` and `L̄`
   both recognised by `n`-state NFAs, but `L` needing `n^{Ω(log n)}` states as a
   UFA. Refutes a conjecture of Colcombet.

plus a bonus result (`parts/applications.tex`) that approximate non-negative
rank admits no efficient error reduction.

All of it runs through communication complexity.

---

## 1. Design principles

### 1.1 Runs are objects, never endpoints

Mathlib's `NFA` gives `evalFrom`: the *set of states* a word can end in. That
determines the recognised language and nothing else this area needs.

Unambiguity is a statement about **runs**. A UFA may reach an accepting state
along two different paths, and it is exactly that which is forbidden. Collapsing
a run to its endpoint would define a strictly weaker class and every theorem here
would be about the wrong objects.

So `NFA.IsRun q w rs` carries the whole trajectory, `rs` listing the states
*after* each letter. Concrete rule: **if a proof only ever mentions `Reach`, it
is a cover argument and belongs on the `Cov` side; the moment it needs
`Unambiguous`, it must be phrased on `IsRun`.**

The start state is deliberately not in `rs`. Keeping `rs.length = w.length`
makes `IsRun` a structural recursion on the word with no side condition, and
makes `isRun_append` an `List.append` statement on the nose. The price is that
the final state is `lastState q rs`, defined by the matching recursion so that
both its equations are `rfl`.

### 1.2 Imported results are hypotheses, never axioms

Same discipline as [`KnowledgeCompilation-ROADMAP.md`](KnowledgeCompilation-ROADMAP.md) §1.3, and for the same
reason. Two results are genuinely imported (§3), and both are `structure`s
threaded explicitly into the theorems that consume them.

**And both are inhabited.** A bundle whose fields were jointly unsatisfiable
would make every theorem taking it vacuously true, and `#print axioms` cannot
detect that. `Imported.unambiguousDNFHardCNF_witness` and
`Imported.nondetLifting_witness` are minimal witnesses; they say nothing about
the quantitative content, which is the imported theorem, but they establish that
the conditionals are about something. Both are simultaneously inhabitable at
`κ = Fin 1`, so `Complement.complement_state_separation` in particular is checked non-vacuous.

### 1.3 Explicit bounds, never `Õ` / `Ω̃`

The paper is written in tilde notation throughout, but its proofs produce
explicit expressions. Those are what get stated. Consequence: the final
repackaging `2^{Ω̃(k²)} = N^{Ω̃(log N)}` is **deliberately not formalized** —
see §5.

---

## 2. Module plan

| Module | Contents | Status |
| --- | --- | --- |
| `Basic` | `NFA`, `IsRun`, `lastState`, `isRun_append`, `Reach`, `Accepts`, `Unambiguous`, `IsDFA`, `IsDFA.unambiguous` | **done** |
| `Simulation` | `lem: NFA-CC` (`Cov₁ ≤ s`) and `lem: UFA-CC` (`Par₁ ≤ s`), on `WordsOfLen` | **done** — see §4 |
| `DNFtoUFA` | unambiguous `k`-DNF ⟶ UFA with exactly `ℓ·(n+1)` states | **done** |
| `WordCoding` | gadget variables ↔ split words, and the transport between the two models | **done** — the step the paper omits |
| `Imported` | Balodis et al. Theorem 1; Göös Theorem 4 (non-deterministic lifting) | **done**, both inhabited |
| `Complement` | `thm: complement` | **done** |
| `Union` | `thm: union`, `thm: or` | **done** |
| `Disjointness` | `thm: separation`; Razborov's covering-set lemma | **done** apart from the optional NFA constructions, see §6 |
| `ErrorReduction` | the upper-bound half of `thm: error` | **done** |

---

## 3. Imported results

**A1 — unambiguous DNF versus CNF width** (`thm: Puzzle-I`,
`parts/complementation.tex:22`), from Balodis–Ben-David–Göös–Jain–Kothari,
*Unambiguous DNFs and Alon–Saks–Seymour*, FOCS 2021. *For every `k` there is
`f` on `n ≤ poly(k)` variables with `UC₁(f) ≤ k` and `C₀(f) ≥ Ω̃(k²)`.*

In Lean as `Imported.UnambiguousDNFHardCNF`. Two things are pinned down that the
paper leaves loose. `C₀` needs **no CNF datatype**: the paper's own identity
`C₀(f) = C₁(¬f)` (`:22`) lets the hypothesis read "no width-`w` DNF computes
`¬f`", so `Circuits/DNF.lean` is not duplicated. And the bundle carries an
explicit `termBound`, because the imported theorem bounds no term count while
the UFA's state count is proportional to it — the paper repairs this by
re-counting conjunctions of the *composed* formula crudely in terms of `n`
(`:83`), which is both weaker and `n`-dependent.

**A2 — non-deterministic lifting** (`thm: lifting`,
`parts/complementation.tex:41`), from Göös, *Lower bounds for clique vs.
independent set*, FOCS 2015, Theorem 4. *There is a gadget `g` on
`b = Θ(log n)` bits with `Non₀(f ∘ gⁿ) = Ω(C₀(f)·b)`.*

In Lean as `Imported.NondetLifting`. The gadget is **data**, since the
upper-bound half composes with the very same gadget; the logarithm is removed by
stating the conclusion as a lower bound on the cover number itself.

**Not imported, because they are already proved in this repository.** The union
theorem's chain rests on GJPW18 Lemma 8 and GLMWZ16/Kothari lifting, both carried
by `KnowledgeCompilation/LowerBounds/Imported.lean`, with everything between them
proved — including Göös–Kiefer–Yuan's own Lemma 14 in
`Arlib/KnowledgeCompilation/LowerBounds/ConicalJunta.lean` and `Par₁ ≥ rk⁺` in
`Arlib/Communication/NonnegRank.lean`.
`Union.union_state_separation_of_unionHard` connects to `UnionDerived.unionHard_of_imports`,
and the partition-equality side condition is `rfl`.

**A3 — full rank of the `k`-uniform disjointness matrix**
(`parts/separation.tex:28`, cited to Kushilevitz–Nisan Example 2.12).
`Disjointness.DisjFullRank`, one field, inhabited at `k = 0`. This is
Gottlieb-type inclusion-matrix nonsingularity and there is nothing in Mathlib to
build on. Everything else in §5 of the paper is proved.

---

## 4. `lem: UFA-CC` is not "the same proof"

`parts/union.tex:149` says the UFA simulation lemma is "proved the same way as"
the NFA one. It is not, and the gap is worth recording because it is exactly the
`Cov`/`Par` distinction.

Unambiguity equates the two accepting runs on `x ++ y` *as lists of states*. It
does **not** say that the two rectangle memberships split that common run at the
same place. Closing it needs a fact about the *inputs* rather than the automaton:
both left factors are runs over `x`, so `IsRun.length` gives them equal length and
`List.append_inj` forces them equal, whence the two cut states agree. That is
`NFA.simCutState_unique`.

This is the only place in `Simulation.lean` where the fixed lengths carried by
`WordsOfLen` are used at all. Without them the family is still a cover but need
not be a partition.

---

## 5. Asymptotics

The three headline theorems are stated with explicit bounds. `thm: complement`,
for instance, gives an upper bound of
`termBound · (2^{2b})^k · (2·(|κ|·b) + 1)` states on the UFA — terms of `f`, ways
to expand a width-`k` term into gadget minterms, and word positions plus one —
against a lower bound of `liftBound cnfBound` on any NFA for the complement.

Converting to `N^{Ω̃(log N)}` means substituting `n ≤ poly(k)` and absorbing
constants. It is not done, for the same reason
[`KnowledgeCompilation-ROADMAP.md`](KnowledgeCompilation-ROADMAP.md) §5 gives: the explicit inequality is stronger,
checkable, and does not hide which constants were traded. Note that `n ≤ poly(k)`
from A1 is used *nowhere else* — it only matters for that repackaging.

---

## 6. Open ends

- **The NFAs of `lem: separation`** (`parts/separation.tex:36,:40`). The paper
  also builds polynomial-size NFAs for `⟨Disj^n_k⟩` and its complement, from the
  covering family `Disjointness.exists_sepFamily` — which *is* proved. What is
  missing is the word encoding `⟨S⟩⟨T⟩ ∈ {0,1}^{2n}` and the state count of the
  automaton that guesses `i` and verifies `S ⊆ Z_i`, `Z_i ∩ T = ∅` letterwise.
  Everything it needs is present.
- **`cl: or` in its degree form** (`parts/applications.tex:9`). Only the matrix
  version is formalized. The proof is literally the same one; it belongs on the
  conical-junta side, in `Arlib/KnowledgeCompilation/LowerBounds/ConicalJunta.lean`.
- **`thm: error` end to end.** `ErrorReduction` supplies the `1/4` upper bound
  generically in `F`; instantiating it at §4's hard function to get the stated
  gap is a short assembly that has not been written.
- ~~**Promoting `Communication/`.**~~ **Done.** The machinery used to live at
  `Arlib.KnowledgeCompilation.Communication`; it is now its own area,
  `Arlib.Communication`, which this area and `Arlib.KnowledgeCompilation` both
  depend on. See `MIGRATION.md`.

---

## 7. Deliberately absent

- **A `Language` algebra.** `NFA.language` exists and nothing uses it. The
  theorems are about state counts, and every statement is phrased directly on
  `Accepts`. Closure constructions (product, complement, union) would be needed
  only to reproduce the paper's length-counter step — which turned out to be
  unnecessary; see `Complement.lean`'s docstring.
- **`Fintype` on `Basic`.** Finiteness enters only where a count is needed, in
  `Simulation` and `DNFtoUFA`. Nothing about runs or unambiguity requires it.
