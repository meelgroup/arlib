/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.KnowledgeCompilation.BranchingPrograms.DecisionDNNFCompile
import Arlib.KnowledgeCompilation.BranchingPrograms.TreeProduct
import Arlib.KnowledgeCompilation.BranchingPrograms.Separation

/-!
# Route B: discharging the Oztok–Darwiche bundle on the concrete `T_r(P_{2p})` class

The general `OztokDarwiche` bundle would need an infinite→finite rooting of an arbitrary tree
decomposition (Mathlib has no treewidth API).  Instead we wrap the *explicit* finite
decomposition of `binTree r □ pathGraph (2p)` (`TreeProduct.treewidthLe_binTree_boxProd`) as a
`RootedTD`, then feed it to the sharp compiler `exists_decisionDNNF_of_rootedTD_sharp` — yielding
an **unconditional** decision-DNNF for `φ(T_r(P_{2p}))`.

The one real construction is a heap-style index `BinTreeNode r ≃ Fin (2^{r+1}-1)` under which the
tree-parent (list `tail`) has strictly smaller index — supplying `RootedTD.parent_lt`.
-/

namespace Arlib.KnowledgeCompilation.DecisionDNNF.OztokDarwiche

open Arlib.KnowledgeCompilation.TreeProduct
open Arlib.KnowledgeCompilation.DecisionDNNF.Compile

/-! ## Step 1: the heap index -/

/-- **Heap index of a `Bool`-list**: the position of the node (read up-to-root as a list of turns)
in the array embedding of a complete binary tree.  `[] ↦ 0`, and prepending a turn `b` sends
index `h` to `2h+1` (left) or `2h+2` (right). -/
def heapIdxL : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * heapIdxL l + (if b then 2 else 1)

@[simp] theorem heapIdxL_nil : heapIdxL [] = 0 := rfl

theorem heapIdxL_cons (b : Bool) (l : List Bool) :
    heapIdxL (b :: l) = 2 * heapIdxL l + (if b then 2 else 1) := rfl

/-- **Parent has smaller index**: dropping the most recent turn strictly decreases the index. -/
theorem heapIdxL_tail_lt : ∀ {l : List Bool}, l ≠ [] → heapIdxL l.tail < heapIdxL l
  | [], h => absurd rfl h
  | b :: l, _ => by
      rw [List.tail_cons, heapIdxL_cons]
      rcases b <;> simp <;> omega

/-- **Range bound**: a node at depth `≤ len` has index `< 2^{len+1}-1`. -/
theorem heapIdxL_lt : ∀ (l : List Bool), heapIdxL l < 2 ^ (l.length + 1) - 1
  | [] => by simp
  | b :: l => by
      have ih := heapIdxL_lt l
      rw [heapIdxL_cons]
      simp only [List.length_cons]
      have hpow : 2 ^ (l.length + 1 + 1) = 2 * 2 ^ (l.length + 1) := by ring
      have h1 : 1 ≤ 2 ^ (l.length + 1) := Nat.one_le_two_pow
      rcases b <;> simp <;> omega

/-- **Injectivity**: distinct `Bool`-lists get distinct heap indices. -/
theorem heapIdxL_injective : Function.Injective heapIdxL := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ h
      rcases l₂ with _ | ⟨b, l⟩
      · rfl
      · rw [heapIdxL_nil, heapIdxL_cons] at h; rcases b <;> simp at h <;> omega
  | cons b₁ l₁ ih =>
      intro l₂ h
      rcases l₂ with _ | ⟨b₂, l₂⟩
      · rw [heapIdxL_nil, heapIdxL_cons] at h; rcases b₁ <;> simp at h <;> omega
      · rw [heapIdxL_cons, heapIdxL_cons] at h
        have hb : b₁ = b₂ := by
          rcases b₁ <;> rcases b₂ <;> simp at h ⊢ <;> omega
        subst hb
        have hl : heapIdxL l₁ = heapIdxL l₂ := by rcases b₁ <;> simp at h <;> omega
        rw [ih hl]

/-- The heap index as an element of `Fin (2^{r+1}-1)`. -/
def heapIdx {r : ℕ} (v : BinTreeNode r) : Fin (2 ^ (r + 1) - 1) :=
  ⟨heapIdxL v.1, by
    have h1 := heapIdxL_lt v.1
    have h2 : v.1.length + 1 ≤ r + 1 := by have := v.2; omega
    have h3 : (2 : ℕ) ^ (v.1.length + 1) ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) h2
    omega⟩

theorem heapIdx_injective {r : ℕ} : Function.Injective (heapIdx (r := r)) := by
  intro v w h
  exact Subtype.ext (heapIdxL_injective (Fin.val_eq_of_eq h))

/-- **The heap-index bijection** `BinTreeNode r ≃ Fin (2^{r+1}-1)`: injective into an equicardinal
finite type (`card_binTreeNode`). -/
noncomputable def heapEquiv (r : ℕ) : BinTreeNode r ≃ Fin (2 ^ (r + 1) - 1) :=
  Equiv.ofBijective heapIdx
    ((Fintype.bijective_iff_injective_and_card heapIdx).mpr
      ⟨heapIdx_injective, by rw [card_binTreeNode, Fintype.card_fin]⟩)

@[simp] theorem heapEquiv_apply (r : ℕ) (v : BinTreeNode r) : heapEquiv r v = heapIdx v := rfl

/-! ## Step 2a: the parent function and its suffix characterization -/

/-- The tree node indexed by `k`. -/
noncomputable abbrev nd (r : ℕ) (k : Fin (2 ^ (r + 1) - 1)) : BinTreeNode r := (heapEquiv r).symm k

/-- The root index. -/
noncomputable def rootIdx (r : ℕ) : Fin (2 ^ (r + 1) - 1) := heapEquiv r ⟨[], by simp⟩

@[simp] theorem nd_heapEquiv (r : ℕ) (v : BinTreeNode r) : nd r (heapEquiv r v) = v :=
  (heapEquiv r).symm_apply_apply v

/-- The parent-pointer function on `Fin (2^{r+1}-1)`: `none` at the root, else the index of the
tree parent (`binTreeParent`). -/
noncomputable def boxParent (r : ℕ) (k : Fin (2 ^ (r + 1) - 1)) : Option (Fin (2 ^ (r + 1) - 1)) :=
  if (nd r k).1 = [] then none else some (heapEquiv r (binTreeParent (nd r k)))

theorem boxParent_some_iff (r : ℕ) (k m : Fin (2 ^ (r + 1) - 1)) :
    boxParent r k = some m ↔ (nd r k).1 ≠ [] ∧ nd r m = binTreeParent (nd r k) := by
  unfold boxParent
  by_cases h : (nd r k).1 = []
  · simp [h]
  · simp only [h, if_false, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨h, by rw [nd_heapEquiv]⟩
    · rintro ⟨-, hm⟩; rw [← hm, Equiv.apply_symm_apply]

theorem boxParent_none_iff (r : ℕ) (k : Fin (2 ^ (r + 1) - 1)) :
    boxParent r k = none ↔ (nd r k).1 = [] := by
  unfold boxParent; by_cases h : (nd r k).1 = [] <;> simp [h]

/-- **Ancestry is list-suffix**: reachability by the parent step means the ancestor's list is a
suffix of the descendant's.  Forward direction: each parent step drops the head (`tail`). -/
theorem suffix_of_reflTrans (r : ℕ) {j c : Fin (2 ^ (r + 1) - 1)}
    (h : Relation.ReflTransGen (fun a b => boxParent r a = some b) j c) :
    (nd r c).1 <:+ (nd r j).1 := by
  induction h with
  | refl => exact List.suffix_refl _
  | @tail m c _ hmc ih =>
      have hm := ((boxParent_some_iff r m c).mp hmc).2
      have hstep : (nd r c).1 = (nd r m).1.tail := by rw [hm]; rfl
      rw [hstep]
      exact (List.tail_suffix _).trans ih

/-- Backward direction: a suffix relation is realised by a parent chain. -/
theorem reflTrans_of_suffix (r : ℕ) : ∀ {j c : Fin (2 ^ (r + 1) - 1)},
    (nd r c).1 <:+ (nd r j).1 →
    Relation.ReflTransGen (fun a b => boxParent r a = some b) j c := by
  intro j
  generalize hL : (nd r j).1 = L
  induction L using List.rec generalizing j with
  | nil =>
      intro c hsuf
      have hc : (nd r c).1 = [] := List.eq_nil_of_suffix_nil hsuf
      have : nd r c = nd r j := Subtype.ext (hc.trans hL.symm)
      have : c = j := (heapEquiv r).symm.injective this
      exact this ▸ Relation.ReflTransGen.refl
  | cons b tl ih =>
      intro c hsuf
      rcases List.suffix_cons_iff.mp hsuf with heq | hsuf'
      · have : nd r c = nd r j := Subtype.ext (heq.trans hL.symm)
        have : c = j := (heapEquiv r).symm.injective this
        exact this ▸ Relation.ReflTransGen.refl
      · -- (nd r c).1 <:+ tl = (nd r (parent j)).1
        have hpar : boxParent r j = some (heapEquiv r (binTreeParent (nd r j))) :=
          (boxParent_some_iff r j _).mpr ⟨by simp [hL], nd_heapEquiv r (binTreeParent (nd r j))⟩
        have hnp : (nd r (heapEquiv r (binTreeParent (nd r j)))).1 = tl := by
          rw [nd_heapEquiv]; show (nd r j).1.tail = tl; rw [hL, List.tail_cons]
        exact Relation.ReflTransGen.head hpar (ih hnp hsuf')

/-! ## Step 2b: bags, index value, and the `RootedTD` instance -/

/-- Bag membership: `v` is in the bag of `k` iff its tree coordinate is `k`'s node or its parent. -/
theorem mem_boxBag (r p : ℕ) (k : Fin (2 ^ (r + 1) - 1)) (v : BinTreeNode r × Fin (2 * p)) :
    v ∈ (insert (nd r k) {binTreeParent (nd r k)}) ×ˢ (Finset.univ : Finset (Fin (2 * p)))
      ↔ (v.1 = nd r k ∨ v.1 = binTreeParent (nd r k)) := by
  rw [Finset.mem_product]
  simp [Finset.mem_insert, Finset.mem_singleton]

/-- The list of a bag member is a suffix of the node's list (`v.1 = node` or its `tail`). -/
theorem boxBag_suffix (r p : ℕ) (k : Fin (2 ^ (r + 1) - 1)) (v : BinTreeNode r × Fin (2 * p))
    (h : v ∈ (insert (nd r k) {binTreeParent (nd r k)}) ×ˢ (Finset.univ : Finset (Fin (2 * p)))) :
    v.1.1 <:+ (nd r k).1 := by
  rcases (mem_boxBag r p k v).mp h with h1 | h1
  · rw [h1]
  · rw [h1]; exact List.tail_suffix _

/-- The `Fin` index equals the heap index of its node's list. -/
theorem idx_val (r : ℕ) (k : Fin (2 ^ (r + 1) - 1)) : (k : ℕ) = heapIdxL (nd r k).1 := by
  conv_lhs => rw [← (heapEquiv r).apply_symm_apply k]
  rfl

/-- Bag of node `k` (the concrete decomposition). -/
noncomputable def boxBag (r p : ℕ) (k : Fin (2 ^ (r + 1) - 1)) :
    Finset (BinTreeNode r × Fin (2 * p)) :=
  (insert (nd r k) {binTreeParent (nd r k)}) ×ˢ (Finset.univ : Finset (Fin (2 * p)))

theorem mem_boxBag' (r p : ℕ) (k : Fin (2 ^ (r + 1) - 1)) (v : BinTreeNode r × Fin (2 * p)) :
    v ∈ boxBag r p k ↔ (v.1 = nd r k ∨ v.1 = binTreeParent (nd r k)) := mem_boxBag r p k v

theorem boxRootedTD_parent_lt (r p : ℕ) (k m : Fin (2 ^ (r + 1) - 1))
    (h : boxParent r k = some m) : m < k := by
  obtain ⟨hne, hm⟩ := (boxParent_some_iff r k m).mp h
  have hmv : (m : ℕ) = heapIdxL (nd r k).1.tail := by rw [idx_val r m, hm]; rfl
  have hkv : (k : ℕ) = heapIdxL (nd r k).1 := idx_val r k
  have hlt := heapIdxL_tail_lt hne
  exact Fin.lt_def.mpr (by omega)

theorem boxRootedTD_mem_bag (r p : ℕ) (v : BinTreeNode r × Fin (2 * p)) :
    ∃ k, v ∈ boxBag r p k :=
  ⟨heapEquiv r v.1, (mem_boxBag' r p _ v).mpr (Or.inl (by rw [nd_heapEquiv]))⟩

theorem boxRootedTD_conn_root (r p : ℕ) (rr rr' : Fin (2 ^ (r + 1) - 1))
    (hr : boxParent r rr = none) (hr' : boxParent r rr' = none) : rr = rr' := by
  have h1 : (nd r rr).1 = [] := (boxParent_none_iff r rr).mp hr
  have h2 : (nd r rr').1 = [] := (boxParent_none_iff r rr').mp hr'
  exact (heapEquiv r).symm.injective (Subtype.ext (h1.trans h2.symm))

theorem boxRootedTD_conn_meet (r p : ℕ) (v : BinTreeNode r × Fin (2 * p))
    (i c c' : Fin (2 ^ (r + 1) - 1)) (hc : boxParent r c = some i) (hc' : boxParent r c' = some i)
    (hne : c ≠ c') (hvc : v ∈ boxBag r p c) (hvc' : v ∈ boxBag r p c') : v ∈ boxBag r p i := by
  obtain ⟨_, hic⟩ := (boxParent_some_iff r c i).mp hc
  obtain ⟨_, hic'⟩ := (boxParent_some_iff r c' i).mp hc'
  rcases (mem_boxBag' r p c v).mp hvc with h1 | h1
  · rcases (mem_boxBag' r p c' v).mp hvc' with h2 | h2
    · exact absurd ((heapEquiv r).symm.injective (h1.symm.trans h2)) hne
    · exact (mem_boxBag' r p i v).mpr (Or.inl (h2.trans hic'.symm))
  · exact (mem_boxBag' r p i v).mpr (Or.inl (h1.trans hic.symm))

theorem boxRootedTD_edge_bag (r p : ℕ) :
    ∀ ⦃u v : BinTreeNode r × Fin (2 * p)⦄,
      (binTree r □ SimpleGraph.pathGraph (2 * p)).Adj u v →
      ∃ k, u ∈ boxBag r p k ∧ v ∈ boxBag r p k := by
  rintro ⟨t, x⟩ ⟨t', x'⟩ hadj
  simp only [SimpleGraph.boxProd_adj] at hadj
  rcases hadj with ⟨hT, rfl⟩ | ⟨-, rfl⟩
  · rcases hT with ⟨b, hb⟩ | ⟨b, hb⟩
    · have hp : binTreeParent t' = t := Subtype.ext (by simp [binTreeParent, hb])
      exact ⟨heapEquiv r t',
        (mem_boxBag' r p _ _).mpr (Or.inr (by rw [nd_heapEquiv, hp])),
        (mem_boxBag' r p _ _).mpr (Or.inl (by rw [nd_heapEquiv]))⟩
    · have hp : binTreeParent t = t' := Subtype.ext (by simp [binTreeParent, hb])
      exact ⟨heapEquiv r t,
        (mem_boxBag' r p _ _).mpr (Or.inl (by rw [nd_heapEquiv])),
        (mem_boxBag' r p _ _).mpr (Or.inr (by rw [nd_heapEquiv, hp]))⟩
  · exact ⟨heapEquiv r t,
      (mem_boxBag' r p _ _).mpr (Or.inl (by rw [nd_heapEquiv])),
      (mem_boxBag' r p _ _).mpr (Or.inl (by rw [nd_heapEquiv]))⟩

/-- **The gateway/running-intersection field** for the concrete decomposition.  The nodes whose
bag contains a fixed vertex `(a,·)` are `a` and its two children — a connected star — so a node
`c` reachable from a bag-carrier `x` but not from a carrier `y` must itself be a carrier.  Proved
by the `ReflTransGen↔suffix` translation plus a length argument on the two-element bags. -/
theorem boxRootedTD_running (r p : ℕ) (v : BinTreeNode r × Fin (2 * p))
    (x y c : Fin (2 ^ (r + 1) - 1))
    (hxc : Relation.ReflTransGen (fun a b => boxParent r a = some b) x c)
    (hyc : ¬ Relation.ReflTransGen (fun a b => boxParent r a = some b) y c)
    (hvx : v ∈ boxBag r p x) (hvy : v ∈ boxBag r p y) : v ∈ boxBag r p c := by
  have hsc : (nd r c).1 <:+ (nd r x).1 := suffix_of_reflTrans r hxc
  have hax : v.1.1 <:+ (nd r x).1 := boxBag_suffix r p x v hvx
  have hay : v.1.1 <:+ (nd r y).1 := boxBag_suffix r p y v hvy
  have hxlen : (nd r x).1.length ≤ v.1.1.length + 1 := by
    rcases (mem_boxBag' r p x v).mp hvx with h | h <;> rw [h]
    · omega
    · show (nd r x).1.length ≤ (nd r x).1.tail.length + 1
      rw [List.length_tail]; omega
  rcases List.suffix_or_suffix_of_suffix hsc hax with hca | hac
  · exact absurd (reflTrans_of_suffix r (hca.trans hay)) hyc
  · have hcx_len : (nd r c).1.length ≤ (nd r x).1.length := hsc.length_le
    have hac_len : v.1.1.length ≤ (nd r c).1.length := hac.length_le
    rcases Nat.lt_or_ge v.1.1.length (nd r c).1.length with hlen | hlen
    · have hlen1 : (nd r c).1.length = v.1.1.length + 1 := by omega
      obtain ⟨pre, hpre⟩ := hac
      have hprelen : pre.length = 1 := by
        rw [← hpre, List.length_append] at hlen1; omega
      obtain ⟨b, rfl⟩ := List.length_eq_one.mp hprelen
      have hct : (nd r c).1.tail = v.1.1 := by rw [← hpre]; rfl
      exact (mem_boxBag' r p c v).mpr (Or.inr (Subtype.ext hct.symm))
    · have heq : v.1.1 = (nd r c).1 := hac.eq_of_length (by omega)
      exact absurd (reflTrans_of_suffix r (heq ▸ hay)) hyc

/-- **The explicit rooted tree decomposition of `binTree r □ pathGraph (2p)`.**  The `2^{r+1}−1`
tree nodes are the nodes of the complete binary tree of depth `r` (heap-indexed), each carrying
the two-element bag `{node, parent} × (path)`; width `4p − 1`.  This wraps the concrete
decomposition of `treewidthLe_binTree_boxProd` as a `RootedTD`, so it can be fed to the sharp
Oztok–Darwiche compiler. -/
noncomputable def boxRootedTD (r p : ℕ) :
    RootedTD (binTree r □ SimpleGraph.pathGraph (2 * p)) where
  n := 2 ^ (r + 1) - 1
  bag := boxBag r p
  parent := boxParent r
  parent_lt := boxRootedTD_parent_lt r p
  mem_bag := boxRootedTD_mem_bag r p
  edge_bag := boxRootedTD_edge_bag r p
  running := boxRootedTD_running r p
  conn_meet := boxRootedTD_conn_meet r p
  conn_root := fun _ rr rr' hr hr' _ _ => boxRootedTD_conn_root r p rr rr' hr hr'

@[simp] theorem boxRootedTD_n (r p : ℕ) : (boxRootedTD r p).n = 2 ^ (r + 1) - 1 := rfl

theorem boxRootedTD_widthLe (r p : ℕ) : (boxRootedTD r p).WidthLe (4 * p - 1) := by
  intro k
  show (boxBag r p k).card ≤ (4 * p - 1) + 1
  rw [boxBag, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have h2 : (insert (nd r k) {binTreeParent (nd r k)} : Finset (BinTreeNode r)).card ≤ 2 := by
    apply le_trans (Finset.card_insert_le _ _); simp
  calc (insert (nd r k) {binTreeParent (nd r k)} : Finset (BinTreeNode r)).card * (2 * p)
        ≤ 2 * (2 * p) := Nat.mul_le_mul_right _ h2
    _ ≤ (4 * p - 1) + 1 := by omega

/-- **Step 2 — the unconditional decision-DNNF for `φ(binTree r □ pathGraph 2p)`.**  Feeding the
explicit finite decomposition `boxRootedTD` to the sharp compiler discharges the
`OztokDarwiche` hypothesis: no oracle is assumed.  Size `≤ 15·2^{4p}·(2^{r+1}−1) + 1`. -/
theorem exists_decisionDNNF_binTree_boxProd (r p : ℕ) :
    ∃ C : NNF (BinTreeNode r × Fin (2 * p)),
      IsDecisionDNNF C ∧
      (∀ α, C.eval α = true ↔ phi (binTree r □ SimpleGraph.pathGraph (2 * p)) α) ∧
      C.size ≤ 15 * (2 ^ ((4 * p - 1) + 1) * (2 ^ (r + 1) - 1)) + 1 := by
  have h := exists_decisionDNNF_of_rootedTD_sharp (boxRootedTD r p) (boxRootedTD_widthLe r p)
  rw [boxRootedTD_n] at h
  exact h

/-! ## Step 3: the unconditional quintic separation -/

open Arlib.KnowledgeCompilation

/-- **`Nat.clog 2 r ≤ r`** — the ceiling-log never exceeds its argument, from `r ≤ 2^r`. -/
theorem clog_two_le_self (r : ℕ) : Nat.clog 2 r ≤ r :=
  (Nat.le_pow_iff_clog_le (by norm_num)).mp (le_of_lt (Nat.lt_two_pow_self))

open SimpleGraph in
/-- **Theorem `decisionDNNF_robp_separation` for `T_r(P_{2r})`, fully unconditional.**  This is Razgon's separation
([Raz16, `separ2`]) with *both* sides discharged inside Lean: the
decision-DNNF upper bound comes from `exists_decisionDNNF_binTree_boxProd` (no Oztok–Darwiche
oracle), and the ROBP lower bound from `Razgon.two_rpow_le_size_binTree_pathGraph`.  The only hypothesis is `1 ≤ r`.

With `n = (2^{r+1} − 1)·2r` the number of variables:

* there is a decision-DNNF for `φ(T_r(P_{2r}))` of size `≤ 15·(16·n⁵) + 1` — the paper's `O(n⁵)`;
* every uniform read-once NROBP realising it has real size `≥ 2^{((r+1−⌈log₂ r⌉)·r/2)/f(5)}` —
  the paper's `n^{Ω(log n)}`. -/
theorem decisionDNNF_robp_separation_quintic_unconditional {r : ℕ} (hr : 1 ≤ r) :
    (∃ C : NNF (BinTreeNode r × Fin (2 * r)), IsDecisionDNNF C ∧
        (∀ α, C.eval α = true ↔ phi (binTree r □ SimpleGraph.pathGraph (2 * r)) α) ∧
        C.size ≤ 15 * (16 * ((2 ^ (r + 1) - 1) * (2 * r)) ^ 5) + 1) ∧
      ∀ (s : ℕ) (Z : NROBP (BinTreeNode r × Fin (2 * r)) s),
        Z.ReadOnce → Z.Uniform →
        Z.Realises (binTree r □ SimpleGraph.pathGraph (2 * r)) →
        (2 : ℝ) ^ ((((r + 1 - Nat.clog 2 r) * r / 2 : ℕ) : ℝ) / TCover.f 5) ≤ (s : ℝ) := by
  haveI : DecidableRel (binTree r □ SimpleGraph.pathGraph (2 * r)).Adj :=
    fun _ _ => Classical.dec _
  refine ⟨?_, fun s Z hro hu hR =>
    Razgon.two_rpow_le_size_binTree_pathGraph (clog_two_le_self r) Z hro hu hR⟩
  obtain ⟨C, hC, hcomp, hsize⟩ := exists_decisionDNNF_binTree_boxProd r r
  refine ⟨C, hC, hcomp, le_trans hsize ?_⟩
  set n : ℕ := (2 ^ (r + 1) - 1) * (2 * r) with hn
  have hpow : 2 ≤ 2 ^ (r + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : (2 ^ (r + 1) - 1) * 2 ≤ n := Nat.mul_le_mul_left _ (by omega)
  have hle : 2 ^ (r + 1) ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hlog : r + 1 ≤ Nat.log 2 n := (Nat.pow_le_iff_le_log (by norm_num) hn0).mp hle
  have ht : 4 * r ≤ 4 * Nat.log 2 n + 4 := by omega
  have hquint : 2 ^ (4 * r) * n ≤ 16 * n ^ 5 := pow_mul_le_of_log_le hn0 ht
  have hcount : 2 ^ (r + 1) - 1 ≤ n := Nat.le_mul_of_pos_right _ (by omega)
  have hexp : (4 * r - 1) + 1 = 4 * r := by omega
  have key : 2 ^ ((4 * r - 1) + 1) * (2 ^ (r + 1) - 1) ≤ 16 * n ^ 5 :=
    calc 2 ^ ((4 * r - 1) + 1) * (2 ^ (r + 1) - 1)
          = 2 ^ (4 * r) * (2 ^ (r + 1) - 1) := by rw [hexp]
      _ ≤ 2 ^ (4 * r) * n := Nat.mul_le_mul_left _ hcount
      _ ≤ 16 * n ^ 5 := hquint
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ key) 1

end Arlib.KnowledgeCompilation.DecisionDNNF.OztokDarwiche
