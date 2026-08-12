/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# An exponential separation by forgetting a single variable (`thm:sep`)

Umut Oztok and Adnan Darwiche, *On Compiling DNNFs without Determinism*
(§4, [OD17, `thm:sep`]).  This file formalizes the paper's main
theoretical separation: there are classes `f_n` and `g_n(·, Z)` with `f_n`
equivalent modulo forgetting `Z` to `g_n`, such that **every** d-DNNF for `f_n` is
exponential while **some** d-DNNF for `g_n` is polynomial.  Forgetting the single
auxiliary variable `Z` from the compact d-DNNF for `g_n` yields a compact
(non-deterministic) DNNF for `f_n`, which no d-DNNF can match.

## The concrete functions ([OD17, §4])

Over an `n × n` Boolean matrix `M` the paper builds:

* `h_n(v)` = "the number of `1`s among the inputs `v` is divisible by 3"
  (`divBy3`);
* `row_n(M) = ⊕ᵢ h_n(Rᵢ)`, the XOR over rows (`rowFn`); `col_n` over columns
  (`colFn`);
* `f_n(M) = row_n(M) ∨ col_n(M)` — the **Sauerhoff function** (`sauerhoffFn`);
* `g_n(M, Z) = (Z ∧ row_n(M)) ∨ (¬Z ∧ col_n(M))` (`gFun`).

The Sauerhoff function is exactly the one Bova–Capelli–Mengel–Slivovsky used to
separate DNNF from d-DNNF, and that is what supplies clause (ii).

## What is *proved here* versus imported

The **heart of this file, proved unconditionally, is
`equivModForget_sauerhoffFn_gFun`**: `f_n ≡ ∃Z. g_n`.  The proof is entirely
structural and turns on one fact — that `row_n` and `col_n` read only the matrix
variables, never `Z`.  Given an assignment `α`, its extension with `Z := true`
makes `g_n` equal to `row_n(α)`
and with `Z := false` equal to `col_n(α)`; so `∃Z. g_n` fires iff
`row_n(α) ∨ col_n(α) = f_n(α)`.  Since `EquivModForget` in `Forgetting.Basic` is
*definitionally* `f(α) ↔ ∃β≡α off Y. g(β)`, this is the whole content, and by
`equivModForget_iff_eq_forgetFun` it upgrades to the equation
`f_n = forgetFun {Z} g_n` (`sauerhoffFn_eq_forgetFun`).  The internal shape of
`h_n` — divisibility by 3, parity of the XOR — is *irrelevant* to this proof, and
is never unfolded; it is defined faithfully only so that the classes are the
paper's.

The **two quantitative facts the paper imports and does not prove** are carried as
`structure` bundles with explicit numeric bounds, exactly in the style of
`LowerBounds/Imported.lean` (`docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3), never as `axiom`s:

* `SauerhoffdDNNFLowerBound n` — clause (ii), Bova–Capelli–Mengel–Slivovsky: every
  d-DNNF computing `f_n` has at least `bound` nodes, where the intended `bound` is
  exponential in `n`.
* `GndDNNFUpperBound n` — clause (iii): `row_n`, `col_n` have polynomial OBDDs (a
  subset of d-DNNF), so `g_n` has a d-DNNF of at most `bound` nodes, `bound`
  polynomial in `n`.

Both bundles are **inhabited** (`sauerhoffdDNNFLowerBound_witness`,
`gndDNNFUpperBound_witness`), so the conditional `thm:sep` is provably not
vacuous.  The lower-bound witness is minimal (`bound = 1`, true because every NNF
has a root and hence at least one node) and asserts nothing about the exponential
content — that is the imported theorem.  The upper-bound witness is at `n = 0`,
where `g_0` collapses to the constant `⊥` and a one-node circuit suffices; that a
single instance is inhabited is all a non-vacuity check needs (compare the
degenerate two-variable witnesses of `LowerBounds/Imported.lean`).

## Adjoining the fresh variable

`M` ranges over `Fin n × Fin n` and `Z` is a single fresh variable, so the ambient
variable type is `SepVar n := (Fin n × Fin n) ⊕ Unit`, with `Z = Sum.inr ()` and
the matrix entry `M(i,j) = α (Sum.inl (i,j))`.  This is the `Sum` idiom the module
docstring of `Forgetting.Basic` points at for adjoining one variable; the forgotten
set is the singleton `{Z}`, matching the paper's "forgetting a single auxiliary
variable".

## The corollary ([OD17, §4])

`exists_dDNNF_gFun_hard_forget` packages the separation as the paper's corollary:
d-DNNF (and FBDD) do not support polynomial-time single-variable forgetting.  It
exhibits the compact d-DNNF for `g_n` whose `{Z}`-forgetting computes `f_n`, together with the
fact that any d-DNNF for that forgotten function is large — so the forgetting
operation cannot be a polynomial-size d-DNNF-to-d-DNNF map.
-/
import Arlib.KnowledgeCompilation.Forgetting.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Arlib.KnowledgeCompilation
namespace Forgetting

open scoped BigOperators

/-! ## The variable type: an `n × n` matrix plus one fresh variable -/

/-- **The ambient variable type** for the separation: the `n × n` matrix
variables `Fin n × Fin n`, together with a single fresh variable `Z` adjoined as
`Sum.inr ()` (§4, [OD17]). -/
abbrev SepVar (n : ℕ) := (Fin n × Fin n) ⊕ Unit

/-- **The auxiliary variable `Z`** — the only variable ever forgotten. -/
def sepZ (n : ℕ) : SepVar n := Sum.inr ()

/-- **The matrix entry `M(i, j)`** read off an assignment: the value `α` gives to
the variable `Sum.inl (i, j)`. -/
def matrixEntry {n : ℕ} (α : SepVar n → Bool) (i j : Fin n) : Bool := α (Sum.inl (i, j))

/-- A matrix variable is never the forgotten variable `Z`. -/
lemma inl_ne_sepZ {n : ℕ} (i j : Fin n) : (Sum.inl (i, j) : SepVar n) ≠ sepZ n := by
  simp [sepZ]

/-! ## The Sauerhoff building blocks -/

/-- **`h_n`** (§4): `true` iff the number of `1`s among the inputs is
divisible by 3.  The internal shape is never used below — the separation depends
only on the fact that `rowFn`/`colFn` ignore `Z`. -/
def divBy3 {n : ℕ} (v : Fin n → Bool) : Bool :=
  decide (3 ∣ ∑ j : Fin n, (if v j then 1 else 0))

/-- **The parity (XOR) of a family of bits**: `true` iff an odd number of them are
`true`.  This is `⊕ᵢ` at [OD17, §4], written as the parity of a cardinality so that no
fold instance is needed. -/
def xorFam {n : ℕ} (f : Fin n → Bool) : Bool :=
  decide (Odd (Finset.univ.filter (fun i => f i = true)).card)

/-- The `h_n`-value of row `i` of the matrix, `h_n(Rᵢ)`. -/
def rowBit {n : ℕ} (α : SepVar n → Bool) (i : Fin n) : Bool :=
  divBy3 (fun j => matrixEntry α i j)

/-- The `h_n`-value of column `i` of the matrix, `h_n(Cᵢ)`. -/
def colBit {n : ℕ} (α : SepVar n → Bool) (i : Fin n) : Bool :=
  divBy3 (fun j => matrixEntry α j i)

/-- **`row_n(M) = ⊕ᵢ h_n(Rᵢ)`** (§4). -/
def rowFn {n : ℕ} (α : SepVar n → Bool) : Bool := xorFam (rowBit α)

/-- **`col_n(M) = ⊕ᵢ h_n(Cᵢ)`** (§4). -/
def colFn {n : ℕ} (α : SepVar n → Bool) : Bool := xorFam (colBit α)

/-- **The Sauerhoff function `f_n(M) = row_n(M) ∨ col_n(M)`** (§4). -/
def sauerhoffFn (n : ℕ) (α : SepVar n → Bool) : Bool := rowFn α || colFn α

/-- **`g_n(M, Z) = (Z ∧ row_n(M)) ∨ (¬Z ∧ col_n(M))`** (§4). -/
def gFun (n : ℕ) (α : SepVar n → Bool) : Bool :=
  (α (sepZ n) && rowFn α) || (!α (sepZ n) && colFn α)

/-! ## `row_n` and `col_n` do not read `Z`

This single fact — the matrix functions are independent of the forgotten variable
— is the whole engine of the equivalence-modulo-forgetting proof. -/

/-- If two assignments agree on every matrix variable, they agree on `matrixEntry`. -/
lemma matrixEntry_congr {n : ℕ} {α β : SepVar n → Bool}
    (h : ∀ i j, α (Sum.inl (i, j)) = β (Sum.inl (i, j))) (i j : Fin n) :
    matrixEntry α i j = matrixEntry β i j := h i j

/-- `row_n` depends only on the matrix variables. -/
lemma rowFn_congr {n : ℕ} {α β : SepVar n → Bool}
    (h : ∀ i j, α (Sum.inl (i, j)) = β (Sum.inl (i, j))) : rowFn α = rowFn β := by
  have : rowBit α = rowBit β := by
    funext i; unfold rowBit; congr 1; funext j; exact matrixEntry_congr h i j
  rw [rowFn, rowFn, this]

/-- `col_n` depends only on the matrix variables. -/
lemma colFn_congr {n : ℕ} {α β : SepVar n → Bool}
    (h : ∀ i j, α (Sum.inl (i, j)) = β (Sum.inl (i, j))) : colFn α = colFn β := by
  have : colBit α = colBit β := by
    funext i; unfold colBit; congr 1; funext j; exact matrixEntry_congr h j i
  rw [colFn, colFn, this]

/-- An assignment agreeing with `α` off `{Z}` agrees with it on every matrix
variable, since matrix variables are never `Z`. -/
lemma matrix_eq_of_off_sepZ {n : ℕ} {α β : SepVar n → Bool}
    (hβ : ∀ x ∉ ({sepZ n} : Finset (SepVar n)), β x = α x) (i j : Fin n) :
    α (Sum.inl (i, j)) = β (Sum.inl (i, j)) :=
  (hβ (Sum.inl (i, j)) (by simp [Finset.mem_singleton, inl_ne_sepZ])).symm

/-! ## The equivalence modulo forgetting — the provable heart of the file -/

/-- **`f_n` is equivalent modulo forgetting `Z` to `g_n`** (§4):
`f_n(M) ≡ ∃Z. g_n(M, Z)`.

The two directions of `EquivModForget` (definition in `Forgetting.Basic`, [OD17, §5.3]):

* If `f_n(α) = row_n(α) ∨ col_n(α)` is `true`, one of the disjuncts holds; extend
  `α` by setting `Z` to `true` (if `row_n`) or `false` (if `col_n`).  The
  extension agrees with `α` off `{Z}`, and by `rowFn_congr`/`colFn_congr` makes
  the matching disjunct of `g_n` fire.
* Conversely any `β` agreeing with `α` off `{Z}` has `row_n(β) = row_n(α)` and
  `col_n(β) = col_n(α)`, so `g_n(β) = true` forces one of `row_n(α)`, `col_n(α)`,
  hence `f_n(α)`. -/
theorem equivModForget_sauerhoffFn_gFun (n : ℕ) :
    EquivModForget {sepZ n} (sauerhoffFn n) (gFun n) := by
  intro α
  constructor
  · intro hf
    rw [sauerhoffFn, Bool.or_eq_true] at hf
    rcases hf with hrow | hcol
    · -- set `Z := true`, making `g_n = row_n`
      refine ⟨Function.update α (sepZ n) true, fun x hx => ?_, ?_⟩
      · exact Function.update_of_ne (by simpa using hx) _ _
      · have hZ : Function.update α (sepZ n) true (sepZ n) = true := Function.update_self _ _ _
        have hr : rowFn (Function.update α (sepZ n) true) = rowFn α :=
          rowFn_congr fun i j =>
            (Function.update_of_ne (by simp [inl_ne_sepZ]) _ _)
        rw [gFun, hZ, hr, hrow]; simp
    · -- set `Z := false`, making `g_n = col_n`
      refine ⟨Function.update α (sepZ n) false, fun x hx => ?_, ?_⟩
      · exact Function.update_of_ne (by simpa using hx) _ _
      · have hZ : Function.update α (sepZ n) false (sepZ n) = false := Function.update_self _ _ _
        have hc : colFn (Function.update α (sepZ n) false) = colFn α :=
          colFn_congr fun i j =>
            (Function.update_of_ne (by simp [inl_ne_sepZ]) _ _)
        rw [gFun, hZ, hc, hcol]; simp
  · rintro ⟨β, hβ, hg⟩
    have hmat : ∀ i j, α (Sum.inl (i, j)) = β (Sum.inl (i, j)) :=
      matrix_eq_of_off_sepZ hβ
    have hr : rowFn β = rowFn α := rowFn_congr fun i j => (hmat i j).symm
    have hc : colFn β = colFn α := colFn_congr fun i j => (hmat i j).symm
    rw [gFun, hr, hc, Bool.or_eq_true] at hg
    rw [sauerhoffFn, Bool.or_eq_true]
    rcases hg with h | h
    · rw [Bool.and_eq_true] at h; exact Or.inl h.2
    · rw [Bool.and_eq_true] at h; exact Or.inr h.2

/-- **The equivalence modulo forgetting, as an equation** (via
`equivModForget_iff_eq_forgetFun`, [OD17, §5.3]):
`f_n = ∃Z. g_n`.  This is the form that plugs into the compilation algorithm —
`forgetNNF` applied to a d-DNNF for `g_n` computes exactly `f_n`. -/
theorem sauerhoffFn_eq_forgetFun (n : ℕ) :
    sauerhoffFn n = forgetFun {sepZ n} (gFun n) :=
  equivModForget_iff_eq_forgetFun.mp (equivModForget_sauerhoffFn_gFun n)

/-! ## The two imported quantitative facts, as hypothesis bundles

Neither is proved by the paper; both are carried as `structure`s with an explicit
numeric bound, in the style of `LowerBounds/Imported.lean` (`docs/dev/KnowledgeCompilation-ROADMAP.md` §1.3), so
that `forgetting_separation` visibly rests on exactly these two hypotheses and on
nothing else.  Both are inhabited below, so the conditional is not vacuous. -/

/-- **Clause (ii) — the d-DNNF lower bound for the Sauerhoff function**
(Bova–Capelli–Mengel–Slivovsky, imported via §4, [OD17]).

Every d-DNNF computing `f_n` has at least `bound` nodes; the imported theorem
supplies a `bound` exponential in `n`.  Following `docs/dev/KnowledgeCompilation-ROADMAP.md` §5 the bound is an
explicit parameter rather than an asymptotic assertion, so a downstream statement
relates the number it is given to the number it produces.

**Not to be proved here** — it is the Bova–Capelli–Mengel–Slivovsky separation of
DNNF from d-DNNF, a substantial paper in its own right, and it carries the entire
quantitative content of the separation. -/
structure SauerhoffdDNNFLowerBound (n : ℕ) where
  /-- The size lower bound; intended to be exponential in `n`. -/
  bound : ℕ
  /-- Every d-DNNF computing `f_n` has at least `bound` nodes. -/
  hard : ∀ C : NNF (SepVar n), C.IsdDNNF → C.Computes (sauerhoffFn n) → bound ≤ C.size

/-- **Clause (iii) — the polynomial d-DNNF for `g_n`** (§4: `row_n` and
`col_n` have polynomial OBDDs, a subset of d-DNNF, so `g_n` does too).

The data is the compact d-DNNF itself, of at most `bound` nodes with `bound`
polynomial in `n`.  As with the lower bound, `bound` is an explicit parameter.

**Not proved here** — the OBDD construction of Bryant for the divisibility/parity
functions and their combination into a d-DNNF for `g_n` is the imported content;
compare `Imported.SDDComplementation`, which is likewise a construction demanded of
the import rather than a shape check. -/
structure GndDNNFUpperBound (n : ℕ) where
  /-- The size upper bound; intended to be polynomial in `n`. -/
  bound : ℕ
  /-- A d-DNNF computing `g_n` with at most `bound` nodes. -/
  witness : ∃ C : NNF (SepVar n), C.IsdDNNF ∧ C.Computes (gFun n) ∧ C.size ≤ bound

/-! ### Non-vacuity of the two bundles -/

/-- **`SauerhoffdDNNFLowerBound` is inhabited**, for every `n`, with the minimal
bound `1`: every NNF has a root and hence at least one node, so `1 ≤ |C|` for
*any* circuit, d-DNNF or not.  This says nothing about the exponential content —
that is the imported theorem — but it establishes that the hypothesis is about
something rather than being jointly unsatisfiable. -/
def sauerhoffdDNNFLowerBound_witness (n : ℕ) : SauerhoffdDNNFLowerBound n where
  bound := 1
  hard := fun C _ _ => by have h := C.root.isLt; omega

/-- **The one-node constant-`⊥` circuit over `SepVar 0`.**  Used only to inhabit
`GndDNNFUpperBound 0`, where `g_0` collapses to the constant `⊥`. -/
def gZeroFalseNNF : NNF (SepVar 0) where
  size := 1
  gate := fun _ => .const false
  child_lt := by intro i j hj; simp [Gate.children_const] at hj
  root := ⟨0, by omega⟩

/-- `g_0` is the constant `⊥`: over the empty index type `Fin 0` both `row_0` and
`col_0` are the empty XOR, i.e. `false`. -/
theorem gFun_zero (α : SepVar 0 → Bool) : gFun 0 α = false := by
  simp [gFun, rowFn, colFn, xorFam]

/-- **`GndDNNFUpperBound` is inhabited** at `n = 0` with bound `1`: the one-node
constant-`⊥` circuit is a d-DNNF (it has no `∧`- or `∨`-node) computing `g_0`.
A single inhabited instance is all a non-vacuity check needs; the interesting
content — a *polynomial* d-DNNF for every `g_n` — is the imported construction. -/
def gndDNNFUpperBound_witness : GndDNNFUpperBound 0 where
  bound := 1
  witness := by
    refine ⟨gZeroFalseNNF, ⟨?_, ?_⟩, ?_, le_refl 1⟩
    · -- decomposable: no `∧`-node
      intro i j k _ hg
      exact absurd hg (by simp [gZeroFalseNNF])
    · -- deterministic: no `∨`-node
      intro i j k _ hg
      exact absurd hg (by simp [gZeroFalseNNF])
    · -- computes `g_0 = ⊥`
      intro α
      rw [gFun_zero, NNF.eval, gZeroFalseNNF.valAt_const (i := gZeroFalseNNF.root) rfl]

/-! ## The separation theorem and its corollary

The capstone `forgetting_separation` below is a three-clause conjunction, so each
of its clauses is available on its own first: clause (i) is
`equivModForget_sauerhoffFn_gFun`, clause (ii) is
`bound_le_size_of_computes_sauerhoffFn` and clause (iii) is
`exists_dDNNF_gFun_size_le`.  The capstone is then literally the triple of the
three, and no consumer ever has to destructure it. -/

/-- **Clause (ii) of `thm:sep`, on its own**: every d-DNNF computing `f_n` has at
least `lb.bound` nodes.  This is the imported lower bound read out of its bundle,
named so that a caller who wants only this half never touches the conjunction. -/
theorem bound_le_size_of_computes_sauerhoffFn {n : ℕ} (lb : SauerhoffdDNNFLowerBound n) :
    ∀ C : NNF (SepVar n), C.IsdDNNF → C.Computes (sauerhoffFn n) → lb.bound ≤ C.size :=
  lb.hard

/-- **Clause (iii) of `thm:sep`, on its own**: some d-DNNF computes `g_n` with at
most `ub.bound` nodes.  This is the imported upper bound read out of its bundle,
named for the same reason as `bound_le_size_of_computes_sauerhoffFn`. -/
theorem exists_dDNNF_gFun_size_le {n : ℕ} (ub : GndDNNFUpperBound n) :
    ∃ C : NNF (SepVar n), C.IsdDNNF ∧ C.Computes (gFun n) ∧ C.size ≤ ub.bound :=
  ub.witness

/-- **`thm:sep`** (§4, [OD17]).

Conditional on the two imported bundles, the three clauses of the paper's theorem
hold simultaneously for the concrete classes `f_n = sauerhoffFn n` and `g_n = gFun n`:

* **(i)** `f_n` is equivalent modulo forgetting `Z` to `g_n` — proved
  unconditionally, `equivModForget_sauerhoffFn_gFun`;
* **(ii)** every d-DNNF computing `f_n` has at least `lb.bound` nodes —
  `bound_le_size_of_computes_sauerhoffFn`;
* **(iii)** some d-DNNF computes `g_n` with at most `ub.bound` nodes —
  `exists_dDNNF_gFun_size_le`.

With `lb.bound` exponential and `ub.bound` polynomial (the intended instantiations
of the imports) this is the exponential separation: no compact d-DNNF for `f_n`,
yet a compact d-DNNF for `g_n` from which forgetting the single variable `Z`
recovers `f_n`.

This statement is a convenience: it is exactly the triple of the three named
clauses above, and it is derived from them. -/
theorem forgetting_separation (n : ℕ) (lb : SauerhoffdDNNFLowerBound n)
    (ub : GndDNNFUpperBound n) :
    EquivModForget {sepZ n} (sauerhoffFn n) (gFun n) ∧
      (∀ C : NNF (SepVar n), C.IsdDNNF → C.Computes (sauerhoffFn n) → lb.bound ≤ C.size) ∧
      (∃ C : NNF (SepVar n), C.IsdDNNF ∧ C.Computes (gFun n) ∧ C.size ≤ ub.bound) :=
  ⟨equivModForget_sauerhoffFn_gFun n, bound_le_size_of_computes_sauerhoffFn lb,
    exists_dDNNF_gFun_size_le ub⟩

/-- **The corollary** (§4): d-DNNF (and FBDD) do not support polynomial-time
single-variable forgetting.

The compact d-DNNF `C` for `g_n` witnesses the failure: forgetting the single
variable `Z` from `C` computes `forgetFun {Z} C.eval = f_n`
(`sauerhoffFn_eq_forgetFun`), yet **every** d-DNNF for that forgotten function has at
least `lb.bound` nodes.  So no polynomial-size d-DNNF-to-d-DNNF forgetting operation
can exist: it would turn the `≤ ub.bound`-node `C` into a `≥ lb.bound`-node result,
and `lb.bound` is exponential while `ub.bound` is polynomial. -/
theorem exists_dDNNF_gFun_hard_forget (n : ℕ) (lb : SauerhoffdDNNFLowerBound n)
    (ub : GndDNNFUpperBound n) :
    ∃ C : NNF (SepVar n), C.IsdDNNF ∧ C.size ≤ ub.bound ∧
      (∀ D : NNF (SepVar n), D.IsdDNNF →
        D.Computes (forgetFun {sepZ n} C.eval) → lb.bound ≤ D.size) := by
  obtain ⟨C, hCd, hCc, hCs⟩ := ub.witness
  have hCeval : C.eval = gFun n := funext hCc
  refine ⟨C, hCd, hCs, fun D hDd hDc => ?_⟩
  apply lb.hard D hDd
  intro α
  rw [hDc α, hCeval, ← sauerhoffFn_eq_forgetFun]

end Forgetting
end Arlib.KnowledgeCompilation
