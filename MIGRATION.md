# MIGRATION — the `api-overhaul` pass

This records every externally visible name change made by the `api-overhaul`
pass, which landed as a single commit on top of `a0ca41b`. It exists so that a
downstream repository importing `arlib` can be updated mechanically: everything
below applies in one step to code written against any commit up to `a0ca41b`.

Four kinds of change landed:

1. **Namespace normalisation** — every declaration moved into the namespace
   matching its module path. Of the 510 declarations that were in the bare
   `Arlib` namespace, **504 left it** (§2.3 says which six stayed and why); the
   normalisation pass moved **1129** declarations in all, and the two module
   moves of §2.4 and §2.5 moved a further 163 and ~160. This is expressed as
   **rules** (§2), not as a row per declaration.
2. **Declaration renames** — 81 declarations changed base name. These need
   exact, per-name substitution (§3).
3. **Module moves** — files that changed path, so `import` lines change (§4).
4. **Deletions** — one, with a named replacement (§5).

One later change is recorded here too, because it is the only one since that pass
that breaks a downstream `import`: the `Arlib.Algorithms` area left arlib for
[arlib-community](https://github.com/meelgroup/arlib-community) (§8).

---

## 1. How to use this document

The fastest path, in this order:

| step | do | section |
| --- | --- | --- |
| 1 | Apply the **namespace rules**. Most of them are prefix substitutions on fully-qualified names, and most call sites never spell the prefix at all — an `open Arlib.Probability` (etc.) fixes those. | §2 |
| 2 | Apply the **rename table** for the areas you use. Do this *after* step 1, or the fully-qualified spellings in the table will not match. | §3 |
| 3 | Fix **imports**. | §4 |
| 4 | Check the **deletion** and the **API-surface changes**. | §5, §6 |
| 5 | Build. If something still fails, §7 lists what is known to be uncertain. | §7 |

Two things to know before you start.

**Order matters, longest-first.** Several old names are prefixes of other old
names (`separ` / `separ2` / `separ2_quintic` / `separ2_quintic_unconditional`;
`thm_main` / `thm_main_instance`; `emf` / `emf_indep`). Sort your substitution
rules by decreasing length of the old name, or use whole-identifier matching.
Every row in §3 whose old name is unsafe as a plain string substitution carries
a flag in the **mechanical?** column. **Those flags are the most valuable thing
in this document** — read them before writing the script.

**Do not touch LaTeX-label citations.** Throughout the library, prose cites the
source paper by its own label: `` `thm: main` ``, `` `thm:sep` ``,
`` `cor: add` ``, `` `cor:fpras-ta-bta` ``, `` `theo:fpras-bta` ``,
`` `lemma:1BP_are_well_structured` ``, `` `corollary:1BP_size_searchvx` ``,
`` `theorem:main_result` ``, and dozens more. These were **deliberately not
renamed** — they are citations, not identifiers, and they are how a reader finds
the statement in the paper. A grep for the old Lean names will still find them.
Leave them alone.

Some paper labels are spelled *exactly* like a Lean identifier and are still
labels: **`dmwtwstruct`, `matchontheway`, `mincase`, `lbengine`.** In particular
`dmwtwstruct` contains `dmwtw`, which *is* a renamed Lean name. Use
whole-identifier matching, or `dmwtwstruct` becomes `razgonGraph_boundsstruct`.

---

## 2. Namespace normalisation

### 2.1 The rule

A declaration's namespace now matches its module path, with one refinement the
repository already stated for itself (`Arlib/Automata/Basic.lean:47`):
**organisational subdirectories add no namespace.** So:

* the **area directory** `Arlib/<Area>/` fixes the namespace root `Arlib.<Area>`;
* subdirectories (`Circuits/`, `LowerBounds/`, `BranchingPrograms/`, `Chains/`,
  `Techniques/`, `Coresets/`, …) contribute nothing;
* **type-API sub-namespaces are kept and re-homed under their area**: `FinProb`,
  `ProbSpace`, `CoinSpace`, `MixedCoinSpace`, `ContCoinProto`, `SecondMoment`,
  `StochApprox`, `KWiseIndep`, `IsIndicatorFamily`, `HittingWeight`, ….

Concretely, if a declaration used to be `Arlib.foo` and its file is under
`Arlib/<Area>/`, it is now `Arlib.<Area>.foo`; and if it used to be
`Arlib.SomeType.foo`, it is now `Arlib.<Area>.SomeType.foo`.

### 2.2 The complete table of affected namespace prefixes

Substitutions on fully-qualified names. Counts are declarations affected.

| old namespace prefix | new namespace prefix | decls | note |
| --- | --- | --- | --- |
| `Arlib.` *(decls from `Arlib/Probability/**`)* | `Arlib.Probability.` | 456 | the bulk of the pass |
| `Arlib.` *(decls from `Arlib/Combinatorics/**`)* | `Arlib.Combinatorics.` | 42 | |
| `Arlib.` *(decls from `Arlib/GameTheory/**`)* | `Arlib.GameTheory.` | 2 | `sum_gamma_sum_r_comm`, `yao_minimax` |
| `Arlib.` *(the 3 trailing theorems of `Arlib/MDP/Termination.lean`)* | `Arlib.MDP.` | 3 | `exists_escapeBound_of_noEC`, `exists_hittingWeight_of_escapeBound`, `exists_hittingWeight_of_noEC` |
| `Arlib.FinProb.` | `Arlib.Probability.FinProb.` | 170 | |
| `Arlib.CoinSpace.` | `Arlib.Probability.CoinSpace.` | 111 | includes `Arlib.CoinSpace.DependsOn.*` |
| `Arlib.MixedCoinSpace.` | `Arlib.Probability.MixedCoinSpace.` | 107 | includes `…MixedCoinSpace.BddMeas.*` |
| `Arlib.ProbSpace.` | `Arlib.Probability.ProbSpace.` | 37 | includes `…ProbSpace.IsAdm.*` |
| `Arlib.ContCoinProto.` | `Arlib.Probability.ContCoinProto.` | 18 | |
| `Arlib.StochApprox.` | `Arlib.Probability.StochApprox.` | 14 | |
| `Arlib.SecondMoment.` | `Arlib.Probability.SecondMoment.` | 9 | |
| `Arlib.KWiseIndep.` | `Arlib.Probability.KWiseIndep.` | 8 | |
| `Arlib.IsIndicatorFamily.` | `Arlib.Probability.IsIndicatorFamily.` | 3 | |
| `Arlib.HittingWeight.` | `Arlib.MDP.HittingWeight.` | 14 | the structure itself moves too: `Arlib.HittingWeight` → `Arlib.MDP.HittingWeight` |
| `Arlib.Approximation.Lewis.` | `Arlib.Approximation.LewisWeights.` | 145 | the namespace was misspelled relative to its directory `LewisWeights/` |
| `Arlib.KnowledgeCompilation.` *(the 163 declarations of the promoted communication modules — §2.4)* | `Arlib.Communication.` | 163 | **not** a blanket rule; see §2.4 |
| `Arlib.KnowledgeCompilation.Tseitin.` *(17 imported bundles — §3.2)* | `Arlib.KnowledgeCompilation.Tseitin.Imported.` | 17 | structures; every projection and constructor moves with its structure |
| `Arlib.MarkovChains.` *(the `FinDist` core — §2.5)* | `Arlib.Probability.` / `Arlib.Probability.FinDist.` / `Arlib.Probability.Coupling.` | ~160 | old spellings still resolve through an `export` shim; see §2.5 |

Unchanged: `Arlib.Probability.*`, `Arlib.Probability.Torus.*`,
`Arlib.Probability.InverseCDF.*`, `Arlib.MarkovChains.*` (everything not in the
`FinDist` core), `Arlib.KnowledgeCompilation.*` (everything not in §2.4),
`Arlib.Automata.*`, `Arlib.Approximation.*` (other than `Lewis`),
`Arlib.Algorithms.TPA.*` (which has since left the repository — §8),
`Arlib.InformationTheory.*`, `Arlib.MDP.*`.

### 2.3 The two deliberate exceptions — bare `Arlib` is not empty

After the pass, bare `Arlib` holds **exactly six declarations**:

| declaration | file | why it stays |
| --- | --- | --- |
| `Arlib.relErr` | `Arlib/Prelude.lean` | `Prelude` is the root module; it has no area. |
| `Arlib.mem_relErr` | `Arlib/Prelude.lean` | " |
| `Arlib.relErr.lower` | `Arlib/Prelude.lean` | " |
| `Arlib.relErr.upper` | `Arlib/Prelude.lean` | " |
| `Arlib.relErr_subset_of_le` | `Arlib/Prelude.lean` | " |
| `Arlib.MDP` *(the `structure`)* | `Arlib/MDP/Basic.lean` | The area namespace and the eponymous type coincide **by design**. Its API sits in `Arlib.MDP.*`, which is exactly the dot-notation namespace of the type, so `M.kernel`, `M.H`, `M.vmax` resolve. Applying the path rule would give `Arlib.MDP.MDP` and silently break every dot-notation call site in the area. This is Mathlib's `Filter` pattern (`Filter` the structure at the root, `Filter.map` the API). |

Do not "fix" either of these.

Note that `Arlib/MDP/HittingWeight.lean` does **not** have that shape — its type
name differs from the directory — so it moved normally to
`Arlib.MDP.HittingWeight`.

### 2.4 `Arlib.KnowledgeCompilation.*` → `Arlib.Communication.*`

This is a namespace substitution with the suffix unchanged, but it applies **only
to the declarations of the promoted modules**. The complete list of moved
top-level identifiers (93 of them; nested names and structure projections follow
their root):

`ApproximatesTP`, `Coverable`, `Covers`, `DependsOn`, `Gadget`,
`HasApproxNNRankLE`, `HasApproxNonnegRankOfSize`, `HasCoverOfSize`,
`HasNNRankLE`, `HasNonnegRankOfSize`, `HasPartitionOfSize`, `HasTPCover`,
`HasTPPartition`, `NonnegRankOne`, `NonnegRankable`, `Partitionable`,
`Partitions`, `Rectangle`, `TPCovers`, `TPPartitions`, `TPRect`, `VarPartition`,
`anRank`, `anRank_le_of`, `bestCov`, `bestCov_le_bestPar`, `bestCov_le_fixedCov`,
`bestCov_le_of_hasCover`, `bestCov_le_two_pow`, `bestPar`, `bestPar_le_fixedPar`,
`bestPar_le_of_hasPartition`, `bestPar_le_two_pow`, `cell`,
`coverable_of_dependsOn`, `dependsOn_const`, `exists_mem_extendFamily`,
`extendFamily`, `extendNonnegFamily`, `extendOn`, `extendOn_apply`, `fiber`,
`fiberIndicator`, `fiberIndicator_apply`, `fiberIndicator_true`, `fixedCov`,
`fixedCov_le_fixedPar`, `fixedCov_le_of_hasCover`, `fixedCov_le_two_pow`,
`fixedNonnegRank`, `fixedNonnegRank_le_fixedPar`,
`fixedNonnegRank_le_of_hasNonnegRank`, `fixedPar`, `fixedPar_le_of_hasPartition`,
`fixedPar_le_two_pow`, `forall_not_hasCover_of_lt_bestCov`,
`forall_not_hasPartitionOfSize_of_forall_not_hasNonnegRankOfSize`,
`forall_not_hasPartition_of_lt_bestPar`,
`hasApproxNonnegRankOfSize_of_hasPartitionOfSize`, `hasCover_fixedCov`,
`hasNNRankLE_of_hasTPPartition`, `hasNonnegRankOfSize_of_hasPartitionOfSize`,
`hasNonnegRankOfSize_of_hasPartitionOfSize_true`, `hasNonnegRank_fixedNonnegRank`,
`hasPartitionOfSize_two_pow`, `hasPartition_fixedPar`,
`le_fixedCov_of_le_bestCov`, `le_fixedPar_of_le_bestPar`,
`le_fixedPar_of_le_fixedNonnegRank`, `mem_extendFamily_iff`, `mem_fiber`,
`mem_padRect_iff`, `nnRank`, `nnRank_le_of`, `nnRank_le_tpPar`,
`not_hasCover_of_lt_fixedCov`, `not_hasNonnegRank_of_lt_fixedNonnegRank`,
`not_hasPartitionOfSize_of_not_hasNonnegRankOfSize`,
`not_hasPartition_of_lt_fixedPar`, `not_hasTPCover_of_lt`,
`not_hasTPPartition_of_lt`, `padRect`, `partitionable_of_dependsOn`,
`sum_eval_extendNonnegFamily`, `tpCov`, `tpCov_le_of_hasTPCover`,
`tpCov_le_tpPar`, `tpFiber`, `tpFiber_apply`, `tpIndicator`,
`tpIndicator_apply`, `tpPar`, `tpPar_le_of_hasTPPartition`.

Structure projections follow the same rule and are not listed separately:
`VarPartition.{X, Y, disj, union_eq}`,
`Rectangle.{left, right, left_congr, right_congr}`,
`NonnegRankOne.{left, right, left_nonneg, right_nonneg, left_congr, right_congr}`,
`TPRect.{left, right}`, and the auto-generated `.mk` / `.rec` / `.injEq`
companions.

> **`DependsOn` is a flag.** There were three `DependsOn`s and there are now two.
> `Arlib.KnowledgeCompilation.DependsOn` → `Arlib.Communication.DependsOn` (with
> `.mono`, `dependsOn_const`, `coverable_of_dependsOn`,
> `partitionable_of_dependsOn`). `Arlib.Probability.CoinSpace.DependsOn` is a
> genuinely different notion (dependence of an *event* on coordinates of a coin
> space) and is untouched apart from the namespace rule in §2.2. The third,
> `Arlib.KnowledgeCompilation.DecisionDNNF.DecisionTree.DependsOn`, was
> **deleted** — see §5.

**Names that did *not* change even though their file moved.** All of
`Arlib.KnowledgeCompilation.ConicalJunta.*` keeps its fully-qualified names; only
its module path changed (§4).

### 2.5 `Arlib.MarkovChains.*` → `Arlib.Probability.*` (the `FinDist` core)

The finite-distribution / finite-kernel core moved out of `Arlib.MarkovChains`
into `Arlib.Probability`, because `Arlib.Probability` could not be allowed to
depend on `Arlib.MarkovChains` and one module did. **No base name changed.** The
namespace mapping:

| old | new | what |
| --- | --- | --- |
| `Arlib.MarkovChains.{IsBilin, psd_cauchy_schwarz, isBilin_weighted}` | `Arlib.Probability.…` | flat → flat |
| `Arlib.MarkovChains.{FinDist, FinKernel, FinChain, finKernel_ext, Stationary, Reversible}` and their sub-namespaces | `Arlib.Probability.…` | flat → flat |
| `Arlib.MarkovChains.X` for every `X` from `Techniques/Functional.lean` (`Ex*`, `ip*`, `Var*`, `relDensity*`, `chiSq*`, `Ex_center`) | `Arlib.Probability.FinDist.X` | flat → `FinDist` |
| `Arlib.MarkovChains.X` for every `X` from the `Pr` / `tvDist` half of `Techniques/TotalVariation.lean` | `Arlib.Probability.FinDist.X` | flat → `FinDist` |
| `Arlib.MarkovChains.Coupling.*`, and the flat helpers `sub_min_eq_max_sub`, `sum_sub_min_left`, `sum_sub_min_right`, `sum_min_eq`, `maxJointFun*`, `maxJoint`, `maximalCoupling*`, `exists_coupling_disagree_eq_*` | `Arlib.Probability.Coupling.*` | flat → `Coupling` |
| `Arlib.MarkovChains.{FinChain.lazy, FinChain.lazy_apply, FinKernel.act_lazy}` | `Arlib.Probability.…` | re-homed so dot notation still works |

**Not moved**, still in `Arlib.MarkovChains`:
`tvDist_iter_push_le`, `MixesWithin`, `MixesWithin.mono_eps`, `MixesWithin.succ`,
`MixesWithin.mono_time`.

> **You probably do not have to do anything here.** Every old
> `Arlib.MarkovChains.*` spelling above is still resolvable, through an `export`
> shim appended to each of the six moved modules. The shim is explicitly
> temporary. Two consequences while it is in place:
>
> * the pretty-printer prefers the shorter alias, so goals and error messages
>   inside `Arlib.Probability` display e.g. `Arlib.MarkovChains.tvDist` for what
>   is really `Arlib.Probability.FinDist.tvDist`;
> * `export` cannot redirect **dot notation**. If you *extend* the `FinKernel` /
>   `FinChain` API with your own dotted declarations, declare them in
>   `Arlib.Probability.FinKernel` / `.FinChain`, not in the `Arlib.MarkovChains`
>   copies, or `P.yourLemma` will not resolve.

> **`tvDist` is a flag.** `Arlib.Probability` now contains two different
> `tvDist`s: the pre-existing `tsum`-based `Arlib.Probability.tvDist`
> (`Arlib/Probability/TVDistance.lean`, on `ι → ℝ`) and the moved
> `Arlib.Probability.FinDist.tvDist` (on `FinDist Ω`). A bare `tvDist` written
> inside `namespace Arlib.Probability` still means the `tsum` one. Do not write a
> blanket `tvDist → FinDist.tvDist` substitution.

---

## 3. Declaration renames

81 declarations changed base name. Grouped by area; a reader who only used one
area only needs one subsection.

The **mechanical?** column says whether the old name is safe as a
whole-identifier substitution over the whole tree.

### 3.1 `Arlib.KnowledgeCompilation` — branching programs (Razgon)

| old fully-qualified name | new fully-qualified name | mechanical? |
| --- | --- | --- |
| `Arlib.KnowledgeCompilation.Asymptotics.dmwtw` | `Arlib.KnowledgeCompilation.Asymptotics.razgonGraph_bounds` | **NO — `dmwtw` is a prefix of `dmwtwstruct`,** which is a *paper label*, not a Lean name, and must survive. Match whole identifiers only. |
| `Arlib.KnowledgeCompilation.Asymptotics.maintheor` | `Arlib.KnowledgeCompilation.Asymptotics.numVertices_rpow_le_size` | **NO — `maintheor` names three different things.** See the box below. |
| `Arlib.KnowledgeCompilation.Razgon.maintheor` | `Arlib.KnowledgeCompilation.Razgon.two_rpow_le_size_binTree_pathGraph` | **NO — see the box below.** |
| `Arlib.KnowledgeCompilation.Equivalence.traditional_maintheor` | `Arlib.KnowledgeCompilation.Equivalence.traditional_two_rpow_le_size_binTree_pathGraph` | **NO — `maintheor` occurs here as a *suffix*.** A rule keyed on `maintheor` will corrupt this name unless it is applied whole-identifier. See the box below. |
| `Arlib.KnowledgeCompilation.Asymptotics.separ` | `Arlib.KnowledgeCompilation.Asymptotics.binTreePathNumVertices_rpow_le_size` | **NO — `separ` is a prefix of `separ2`, `separNumVertices`, `separ_quadratic`, `separ_matching_core`, `separ_exponent_bound`, and a substring of the unrelated word `Separation`** (a namespace, a module name and an English word, all present in the tree). Whole-identifier match, longest-first. |
| `Arlib.KnowledgeCompilation.Asymptotics.separNumVertices` | `Arlib.KnowledgeCompilation.Asymptotics.binTreePathNumVertices` | NO — prefix of `separNumVertices_ne_zero`. Longest-first. |
| `Arlib.KnowledgeCompilation.Asymptotics.separNumVertices_ne_zero` | `Arlib.KnowledgeCompilation.Asymptotics.binTreePathNumVertices_ne_zero` | safe |
| `Arlib.KnowledgeCompilation.Asymptotics.card_separVertex` | `Arlib.KnowledgeCompilation.Asymptotics.card_binTreePathVertex` | safe |
| `Arlib.KnowledgeCompilation.Asymptotics.le_log_separNumVertices` | `Arlib.KnowledgeCompilation.Asymptotics.le_log_binTreePathNumVertices` | safe |
| `Arlib.KnowledgeCompilation.Asymptotics.log_separNumVertices_le` | `Arlib.KnowledgeCompilation.Asymptotics.log_binTreePathNumVertices_le` | safe |
| `Arlib.KnowledgeCompilation.Asymptotics.matchingWidth_separ` | `Arlib.KnowledgeCompilation.Asymptotics.log_binTreePathNumVertices_sq_div_le` | safe (note the new name is *not* formed from the old one) |
| `Arlib.KnowledgeCompilation.Asymptotics.separ_quadratic` | `Arlib.KnowledgeCompilation.Asymptotics.quadratic_bound_aux` — **now `private`** | safe as a rename, but see §6.1: it is no longer reachable from another module. |
| `Arlib.KnowledgeCompilation.Asymptotics.separ_matching_core` | `Arlib.KnowledgeCompilation.Asymptotics.matching_core_aux` — **now `private`** | as above |
| `Arlib.KnowledgeCompilation.Asymptotics.separ_exponent_bound` | `Arlib.KnowledgeCompilation.Asymptotics.exponent_bound_sq_aux` — **now `private`** | as above |
| `Arlib.KnowledgeCompilation.NROBP.tnodecut` | `Arlib.KnowledgeCompilation.NROBP.exists_split_isTNode` | safe |
| `Arlib.KnowledgeCompilation.NROBP.nrobplbdmw` | `Arlib.KnowledgeCompilation.NROBP.le_size_of_matchingWidthGe` | safe |
| `Arlib.KnowledgeCompilation.DecisionDNNF.separ2` | `Arlib.KnowledgeCompilation.DecisionDNNF.decisionDNNF_robp_separation` | **NO — `separ2` is a prefix of `separ2_treeProduct`, `separ2_quintic` and `separ2_quintic_unconditional`.** Longest-first. |
| `Arlib.KnowledgeCompilation.DecisionDNNF.separ2_treeProduct` | `Arlib.KnowledgeCompilation.DecisionDNNF.decisionDNNF_robp_separation_binTree_pathGraph` | safe |
| `Arlib.KnowledgeCompilation.DecisionDNNF.separ2_quintic` | `Arlib.KnowledgeCompilation.DecisionDNNF.decisionDNNF_robp_separation_quintic` | NO — prefix of `separ2_quintic_unconditional`. Longest-first. |
| `Arlib.KnowledgeCompilation.DecisionDNNF.OztokDarwiche.separ2_quintic_unconditional` | `Arlib.KnowledgeCompilation.DecisionDNNF.OztokDarwiche.decisionDNNF_robp_separation_quintic_unconditional` | safe |
| `Arlib.KnowledgeCompilation.Uniformize.CleanPaper` | `Arlib.KnowledgeCompilation.Uniformize.CleanInDegree` | safe |

> **`maintheor` named three declarations.** `Asymptotics.maintheor` (the
> `n^{k/c}` form), `Razgon.maintheor` in `BranchingPrograms/Separation.lean` (the
> explicit `r`, `p` form) and `Equivalence.traditional_maintheor` (which contains
> it as a suffix). They map to three *different* new names. A single
> `maintheor → …` rule is wrong in two of the three cases. Disambiguate by
> namespace before substituting.
>
> The old `Arlib/KnowledgeCompilation/ROADMAP.md` referred to the second of these
> as **`Separation.maintheor`**, after the file it lives in. That was never a
> real Lean name: the declaration is in `namespace Razgon`. The correct new
> spelling is `Razgon.two_rpow_le_size_binTree_pathGraph`.

> **Prose in this area no longer contains the old names at all.** The paper
> labels `dmwtw`, `maintheor`, `separ`, `tnodecut`, `nrobplbdmw`, `separ2` are
> spelled exactly like the Lean identifiers, and every prose occurrence inside
> `BranchingPrograms/` was rewritten to the new Lean name (the `.tex:NNN` line
> citation next to each one still points into the paper). So a grep for those
> strings in `Arlib/KnowledgeCompilation/BranchingPrograms/` returns nothing —
> that is expected, not a miss.

### 3.2 `Arlib.KnowledgeCompilation.Tseitin`

Two theorem renames:

| old fully-qualified name | new fully-qualified name | mechanical? |
| --- | --- | --- |
| `Arlib.KnowledgeCompilation.Tseitin.theorem1` | `Arlib.KnowledgeCompilation.Tseitin.two_pow_le_refutationLen_mul_card` | safe as an identifier match. **Do not** rewrite the English "Theorem 1" in prose — the paper numbering was kept on purpose. |
| `Arlib.KnowledgeCompilation.Tseitin.theorem5` | `Arlib.KnowledgeCompilation.Tseitin.dnnfSizeLe_of_regRefutationLen` | as above, for "Theorem 5" |

Seventeen imported-result bundles moved into a new `Imported` sub-namespace, six
of them with a new name. **Every constructor and field projection moves with its
structure** (`.mk`, `.satisfiable_of_even`, `.bp_le_refutation`,
`.minimal_wellStructured`, `.toDNNF`, `.realize`, `.upper`, `.refute_to_bp`,
`.tw_le_bw`, `.bw_le_tw`, `.charge_split`, `.isSub`, `.count_eq`, `.count`,
`.choose`, `.bound`, `.size_iff`, `.imported`, `.minor`, `.transfer`,
`.exists_minor`, `.card_models`); the field names themselves are unchanged.

All rows share the prefix `Arlib.KnowledgeCompilation.Tseitin.`, elided below.

| old | new | mechanical? |
| --- | --- | --- |
| `Corollary8` | `Imported.RefutationToOneBP` | safe |
| `Lemma10` | `Imported.OneBPToWellStructured` | safe |
| `AlekhnovichR11` | `Imported.AlekhnovichRegRefutationUpper` | safe |
| `LovaszNNW` | `Imported.LovaszNNW` | namespace only |
| `TseitinDNNFLower` | `Imported.TseitinDNNFLower` | namespace only |
| `WellStructuredToDNNF` | `Imported.WellStructuredToDNNF` | namespace only |
| `TseitinSatisfiabilityConverse` | `Imported.TseitinSatisfiabilityConverse` | namespace only |
| `TseitinModelCount` | `Imported.TseitinModelCount` | namespace only |
| `HarveyWood` | `Imported.HarveyWood` | namespace only |
| `VertexSplitEquiv` | `Imported.VertexSplitEquiv` | namespace only |
| `IndepSplitModelCount` | `Imported.IndepSplitModelCount` | namespace only |
| `ThreeConnectedSplitChoice` | `Imported.ThreeConnectedSplitChoice` | namespace only |
| `DNNFtoRectangleGame` | `Imported.DNNFtoRectangleGame` | namespace only |
| `ReduceToZeroCharge` | `Imported.ReduceToZeroCharge` | namespace only |
| `SafeSeparators` | `Imported.SafeSeparators` | namespace only |
| `TopMinorDNNF` | `Imported.TopMinorDNNF` | namespace only |
| `ThreeConnectedTopMinor` | `Imported.ThreeConnectedTopMinor` | namespace only |

Deliberately **not** moved and **not** renamed: the datatype
`Tseitin.Refutation`, the data definition `Tseitin.NeighborPartition`, and the
seven non-vacuity witnesses `tseitinConverse_zero`, `tseitinModelCount_empty`,
`indepSplitModelCount_zero`, `threeConnectedSplitChoice_zero`,
`reduceToZeroCharge_zero`, `safeSeparators`, `topMinorDNNF_id` — only their type
ascriptions were requalified.

> **A bare `Imported.` prefix is now ambiguous in this area.** Both
> `Arlib.KnowledgeCompilation.Imported` and
> `Arlib.KnowledgeCompilation.Tseitin.Imported` exist. Inside the Tseitin
> namespace, a bare `Imported.Foo` reads as the Tseitin one. The two namespaces
> were checked to share no member name, so nothing is currently ambiguous, but
> write `KnowledgeCompilation.Imported.SDDComplementation` in full if you mean
> the outer one.

### 3.3 `Arlib.KnowledgeCompilation` — lower bounds

All rows share the prefix `Arlib.KnowledgeCompilation.`, elided. Note the
namespace is `…KnowledgeCompilation.Separation`, **not**
`…KnowledgeCompilation.LowerBounds.Separation` — subdirectories add no namespace.

| old | new | mechanical? |
| --- | --- | --- |
| `Separation.thm_main` | `Separation.exists_dSDNNF_hard_negation` | NO — `thm_main` is a prefix of `thm_main_instance`. Longest-first. |
| `Separation.thm_sep` | `Separation.exists_dSDNNF_hard_sdd` | **NO — `thm_sep` names two different theorems**: this one and `Forgetting.thm_sep` (§3.4), which maps to `Forgetting.forgetting_separation`. Also a prefix of `thm_sep_instance`. Disambiguate by namespace. |
| `Separation.thm_union` | `Separation.exists_dSDNNF_pair_hard_disjunction` | **NO — `thm_union` names two different theorems**: this one and `Arlib.Automata.Union.thm_union` (§3.5), which maps to `Union.union_state_separation`. Also a prefix of `thm_union_instance` and `thm_union_of_primitive_imports`. Disambiguate by namespace. |
| `Separation.thm_ex` | `Separation.exists_dSDNNF_hard_existsFresh` | safe |
| `Separation.cor_add` | `Separation.exists_dSDAC_pair_hard_sum` | NO — prefix of `cor_add_positive` and `cor_add_instance`. Longest-first. |
| `Separation.cor_add_positive` | `Separation.exists_dSDACp_pair_hard_sum` | safe |
| `Instance.thm_main_instance` | `Instance.exists_dSDNNF_hard_negation` | safe |
| `Instance.thm_sep_instance` | `Instance.exists_dSDNNF_hard_sdd` | safe |
| `Instance.thm_union_instance` | `Instance.exists_dSDNNF_pair_hard_disjunction` | safe |
| `Instance.cor_add_instance` | `Instance.exists_dSDACp_pair_hard_sum` | safe |
| `UnionDerived.thm_union_of_primitive_imports` | `UnionDerived.exists_dSDNNF_pair_hard_disjunction_of_imports` | safe |

> **`Instance.*` and `Separation.*` now share base names.** Four pairs collide:
> `exists_dSDNNF_hard_negation`, `exists_dSDNNF_hard_sdd`,
> `exists_dSDNNF_pair_hard_disjunction`, `exists_dSDACp_pair_hard_sum` each exist
> in *both* `Separation` and `Instance`. An unqualified reference that used to be
> unambiguous (`thm_main` could only be the `Separation` one) may now resolve to
> the local `Instance` one. **Qualify every cross-reference.**

### 3.4 `Arlib.KnowledgeCompilation.Forgetting`

All rows share the prefix `Arlib.KnowledgeCompilation.Forgetting.`, elided.

| old | new | mechanical? |
| --- | --- | --- |
| `thm_sep` | `forgetting_separation` | **NO — see the `thm_sep` flag in §3.3.** |
| `cor_forgetting` | `exists_dDNNF_gFun_hard_forget` | safe |
| `mentry` | `matrixEntry` | safe **as a substring** rule: it correctly also turns `mentry_congr` into `matrixEntry_congr`. As a whole-identifier rule you need both rows. |
| `mentry_congr` | `matrixEntry_congr` | safe. *(Not listed in the rename audit; applied as the mechanical follow-on of `mentry`.)* |
| `emf` | `EquivModForget` | **NO. Three separate hazards — see the box below.** |
| `emf_forgetFun` | `equivModForget_forgetFun` | safe |
| `emf_empty` | `equivModForget_empty` | safe |
| `emf_iff_eq_forgetFun` | `equivModForget_iff_eq_forgetFun` | safe |
| `emf_indep` | `equivModForget_indep` | safe |
| `emf_forgetNNF_isDNNF_computes` | `equivModForget_forgetNNF_isDNNF_computes` | safe |
| `emf_sauerhoff_gFun` | `equivModForget_sauerhoffFn_gFun` | safe. **Note the double change** — see the `sauerhoff` box below. |
| `sauerhoff` | `sauerhoffFn` | **NO — see the box below.** |
| `sauerhoff_eq_forgetFun` | `sauerhoffFn_eq_forgetFun` | safe |

> **`emf` — three hazards.**
> 1. `emf` is a prefix of six `emf_*` lemmas, each of which gets the *lowercase*
>    prefix `equivModForget_`, while `emf` itself becomes the *capitalised*
>    `EquivModForget`. A single `emf → EquivModForget` substring rule produces
>    `EquivModForget_indep`, which is wrong. Apply the six `emf_*` rows first, or
>    match whole identifiers.
> 2. `emf` was used **adjectivally in prose**: "`f_n` is emf to `g_n`". That is
>    not a substitution; every such passage was reworded by hand to "is
>    equivalent modulo forgetting `Y` to". If you have prose of your own that
>    says "is emf to", reword it rather than substitute.
> 3. The hypothesis binder `hemf` in `equivModForget_forgetNNF_isDNNF_computes`
>    was **kept**. It is only API through named-argument syntax, but if you call
>    with `(hemf := …)` it still works, and a careless `emf` rule would break it.

> **`sauerhoff` — what changed and what did not.**
> * the *function* `sauerhoff` → `sauerhoffFn`, and `sauerhoff_eq_forgetFun` →
>   `sauerhoffFn_eq_forgetFun`;
> * the *structure* `Forgetting.SauerhoffdDNNFLowerBound` is **unchanged** (the
>   library keeps eponymous names for imported bundles), and therefore so is its
>   inhabitant `Forgetting.sauerhoffdDNNFLowerBound_witness`.
>
> So a substring rule `sauerhoff → sauerhoffFn` is **wrong**: it would corrupt
> `sauerhoffdDNNFLowerBound_witness` into `sauerhoffFndDNNFLowerBound_witness`.
> Match whole identifiers, and list `sauerhoff` and `sauerhoff_eq_forgetFun`
> explicitly.
>
> Also note that the rename audit spelled the composite lemma
> `equivModForget_sauerhoff_gFun`; because the `sauerhoff → sauerhoffFn` rename
> landed in the same pass, the name in the tree is
> **`equivModForget_sauerhoffFn_gFun`**. The tree is authoritative.

### 3.5 `Arlib.Automata`

| old fully-qualified name | new fully-qualified name | mechanical? |
| --- | --- | --- |
| `Arlib.Automata.Complement.thm_complement` | `Arlib.Automata.Complement.complement_state_separation` | safe |
| `Arlib.Automata.Union.thm_union` | `Arlib.Automata.Union.union_state_separation` | **NO — `thm_union` also names `KnowledgeCompilation.Separation.thm_union` (§3.3), which maps elsewhere.** Also a prefix of `thm_union_of_unionHard`. Disambiguate by namespace, longest-first. |
| `Arlib.Automata.Union.thm_union_of_unionHard` | `Arlib.Automata.Union.union_state_separation_of_unionHard` | safe |
| `Arlib.Automata.ErrorReduction.thm_error` | `Arlib.Automata.ErrorReduction.error_reduction_gap` | safe. Do not touch the LaTeX label `` `thm: error` ``. |

### 3.6 `Arlib.Probability`, `Arlib.MDP`, `Arlib.Approximation`

Old names below are the names on `main`; new names include the §2 namespace
change where there was one.

| old fully-qualified name | new fully-qualified name | mechanical? |
| --- | --- | --- |
| `Arlib.ProbSpace.intersection_tail_bound_paper` | `Arlib.Probability.ProbSpace.intersection_tail_bound` | safe, but apply it **before** any rule keyed on the bare `intersection_tail_bound` — the new name is a prefix of the pre-existing `intersection_tail_bound_core`. |
| `Arlib.MDP.H_eq_paper` | `Arlib.MDP.H_eq_sum_target_add_sum_nonterm` | safe |
| `Arlib.Approximation.acjrGamma` | `Arlib.Approximation.failureExponent` | safe **as a substring** rule — it correctly also fixes the four `*acjrGamma*` lemmas below. As a whole-identifier rule, list all five. |
| `Arlib.Approximation.two_rpow_neg_acjrGamma` | `Arlib.Approximation.two_rpow_neg_failureExponent` | NO on its own — prefix of the next two. Longest-first, or use the substring rule. |
| `Arlib.Approximation.two_rpow_neg_acjrGamma_lt` | `Arlib.Approximation.two_rpow_neg_failureExponent_lt` | safe |
| `Arlib.Approximation.two_rpow_neg_acjrGamma_add` | `Arlib.Approximation.two_rpow_neg_failureExponent_add` | safe |
| `Arlib.Approximation.one_le_acjrGamma` | `Arlib.Approximation.one_le_failureExponent` | safe |
| `Arlib.Approximation.acjr_three_budgets` | `Arlib.Approximation.three_budgets_sum` | NO on its own — prefix of `acjr_three_budgets_lt`. The substring rule `acjr_three_budgets → three_budgets_sum` handles both. Does not collide with the pre-existing `three_budgets_div_three`. |
| `Arlib.Approximation.acjr_three_budgets_lt` | `Arlib.Approximation.three_budgets_sum_lt` | safe |
| `Arlib.Approximation.ParsimoniousReduction.fpras` | `Arlib.Approximation.ParsimoniousReduction.isFPRAS_comp` | **NO — see the `fpras` / `fpaus` box below.** |
| `Arlib.Approximation.ParsimoniousReduction.fpaus` | `Arlib.Approximation.ParsimoniousReduction.isFPAUS_comp` | **NO — see the box below.** |
| `Arlib.Approximation.PinnedReduction.fpras` | `Arlib.Approximation.PinnedReduction.isFPRAS_comp_pinned` | **NO — see the box below.** |
| `Arlib.Approximation.PinnedReduction.fpaus` | `Arlib.Approximation.PinnedReduction.isFPAUS_comp_pinned` | **NO — see the box below.** |

> **`fpras` / `fpaus` — four collisions in one word.**
> 1. There are **two** `fpras` and **two** `fpaus`, in `ParsimoniousReduction`
>    and `PinnedReduction`, and they map to *different* names
>    (`isFPRAS_comp` vs `isFPRAS_comp_pinned`). Disambiguate by namespace.
> 2. `\bfpras\b` also matches the LaTeX labels `` `cor:fpras-ta-bta` `` and
>    `` `theo:fpras-bta` ``, which are citations and must not change.
> 3. It is a prefix of two **unrelated** names cited in a docstring in
>    `Approximation/DepSampling.lean:657–658` —
>    `CQCount.Capstone.KAtoms.StarPath.fpras_starFam` and
>    `CQCount.Capstone.KDomain.fprasD_fam`. Those are declarations of a
>    *downstream* project, not of this library, and must not be touched.
> 4. These are structure *fields*, so most call sites spell them as projections
>    (`R.fpras`), not as identifiers.

Four projection lemmas were added beside the unchanged `Arlib.moment_bounds`
(now `Arlib.Probability.moment_bounds`), which is still the simultaneous
four-fold statement — its `Finset.induction_on` step needs all four together.
If you were indexing into it, use these instead:

| positional accessor | named lemma |
| --- | --- |
| `(moment_bounds hind hZ s).1` | `Arlib.Probability.Ex_centre_sum_sq_eq_varSum hind hZ s` |
| `… .2.1` | `Arlib.Probability.abs_Ex_centre_sum_cube_le hind hZ s` |
| `… .2.2.1` | `Arlib.Probability.Ex_centre_sum_pow_four_le hind hZ s` |
| `… .2.2.2` | `Arlib.Probability.Ex_centre_sum_pow_six_le hind hZ s` |

---

## 4. Module moves — `import` paths

| old module | new module | note |
| --- | --- | --- |
| `Arlib.KnowledgeCompilation.Communication.TwoParty` | `Arlib.Communication.TwoParty` | |
| `Arlib.KnowledgeCompilation.Communication.Rectangle` | `Arlib.Communication.Rectangle` | |
| `Arlib.KnowledgeCompilation.Communication.Measures` | `Arlib.Communication.Measures` | |
| `Arlib.KnowledgeCompilation.Communication.NonnegRank` | `Arlib.Communication.NonnegRank` | |
| `Arlib.KnowledgeCompilation.Communication.Gadget` | `Arlib.Communication.Gadget` | |
| `Arlib.KnowledgeCompilation.Basic` | `Arlib.Communication.BooleanFunction` | The module held `DependsOn`, which both `KnowledgeCompilation` and `Automata` need. It was renamed as well as moved, so that the file name says what is in it. |
| `Arlib.KnowledgeCompilation.Communication.ConicalJunta` | `Arlib.KnowledgeCompilation.LowerBounds.ConicalJunta` | Stays in `KnowledgeCompilation` — it is built on `Circuits.DNF`, not on any communication module. **No declaration name in it changed.** |
| `Arlib.MarkovChains.Techniques.Chain` | `Arlib.Probability.FinDist` | |
| `Arlib.MarkovChains.Techniques.Bilinear` | `Arlib.Probability.Bilinear` | |
| `Arlib.MarkovChains.Techniques.Functional` | `Arlib.Probability.FinDistFunctional` | |
| `Arlib.MarkovChains.Techniques.Coupling` | `Arlib.Probability.Coupling` | |
| `Arlib.MarkovChains.Techniques.TotalVariation` | **split three ways** — see below | |

New area root: `Arlib.Communication`. The directory
`Arlib/KnowledgeCompilation/Communication/` no longer exists.

**The `TotalVariation` split.** `Arlib.MarkovChains.Techniques.TotalVariation`
still exists, but holds less:

| content | now in |
| --- | --- |
| the `FinKernel` algebra (`ext'`, `push_comp`, `row_comp`, `push_id`, `comp_assoc`, `id_comp`, `comp_id`, `iter_succ'`) | `Arlib.Probability.FinKernelAlgebra` |
| `Pr`, `tvDist` and everything about them | `Arlib.Probability.FinDistTV` |
| `tvDist_iter_push_le`, `MixesWithin` and its lemmas | still `Arlib.MarkovChains.Techniques.TotalVariation` |

Because the remainder kept the original path, its eleven importers needed no
change.

> **One behaviour change worth flagging.** `import Arlib.KnowledgeCompilation`
> used to pull in the whole communication toolkit — `VarPartition`, `fixedCov`,
> `TPRect` and so on. It now pulls in only what `KnowledgeCompilation` itself
> needs. That still covers `Rectangle`, `Measures`, `NonnegRank` and `Gadget`
> transitively (via `LowerBounds/`), but **not `Arlib.Communication.TwoParty`**,
> which had no `KnowledgeCompilation` consumer. If you used `TPRect`, `tpCov`,
> `tpPar`, `HasTPCover`, `HasTPPartition` or `ApproximatesTP` through
> `import Arlib.KnowledgeCompilation`, add `import Arlib.Communication`.

---

## 5. Deletions

| deleted fully-qualified name | replacement |
| --- | --- |
| `Arlib.SecondMoment.induction_lemma` | Use the two component lemmas directly: **`Arlib.Probability.SecondMoment.G_eq_H_pred`** (`S.G j = S.H (j - 1)`) and **`Arlib.Probability.SecondMoment.H_eq_G`** (`S.H j = S.G j`). Both are public, and both sit immediately above where the deleted declaration was, in `Arlib/Probability/ProbSpaceValidation.lean`. The deleted lemma was a bare rebundling of the two and existed only to be destructured. It had **zero** call sites anywhere in the repository, including markdown. |
| `Arlib.KnowledgeCompilation.DecisionDNNF.DecisionTree.DependsOn` | **`Arlib.Communication.DependsOnList`**, a `List`-indexed derived form of `Arlib.Communication.DependsOn` (`DependsOnList f xs := DependsOn f xs.toFinset`; needs `[DecidableEq V]`). Both old call-site shapes are supported: `dependsOnList_iff` gives the pointwise `∀ x ∈ xs` form a list recursion wants; `dependsOnList_of_forall` and `DependsOnList.apply` are its two halves in applied form; `dependsOnList_toList_iff` bridges to the `Finset` form; `DependsOnList.mono` and `dependsOnList_const` are the `List` twins of the existing lemmas. |

The hypothesis shape (not the meaning, and nothing weakened) of
`DecisionTree.dependsOn_cofactor`, `DecisionTree.dtCore_valAt` and
`DecisionTree.buildDecisionTree_eval` changed with the second of these.

---

## 6. Other API-surface changes

### 6.1 Three lemmas became `private`

`Arlib.KnowledgeCompilation.Asymptotics.quadratic_bound_aux`,
`matching_core_aux` and `exponent_bound_sq_aux` (formerly `separ_quadratic`,
`separ_matching_core`, `separ_exponent_bound`) are now `private` and are **not
reachable from another module**. They were pure-arithmetic step lemmas used only
inside `Asymptotics.lean`. If you were using one, the fix is to restate it
locally; it is not going to come back.

### 6.2 Capstone theorems are now derived from named components

Several theorems whose statement is an anonymous conjunction of three or more
facts used to be the *primary* statement, with consumers destructuring them
(`obtain ⟨-, hdeg, -, hmw⟩ := …`). They are now **derived** from separately named
component lemmas. The capstone statements are unchanged, so nothing breaks — but
if your code indexes into one of these tuples, index into the component instead.
The components are more stable than the tuple layout.

| capstone | components to use instead |
| --- | --- |
| `TreeProduct.binTree_pathGraph_bounds` | `TreeProduct.card_binTree_pathGraph`, `TreeProduct.maxDegreeLe_binTree_pathGraph` (pre-existing), `TreeProduct.treewidthLe_binTree_pathGraph`, `TreeProduct.matchingWidthGe_binTree_pathGraph` |
| `Asymptotics.razgonGraph_bounds` | `Asymptotics.card_vertex` (pre-existing), `Asymptotics.maxDegreeLe_razgonGraph`, `Asymptotics.treewidthLe_razgonGraph`, `Asymptotics.matchingWidthGe_razgonGraph` |
| `Forgetting.forgetting_separation` | `Forgetting.equivModForget_sauerhoffFn_gFun`, `Forgetting.bound_le_size_of_computes_sauerhoffFn`, `Forgetting.exists_dDNNF_gFun_size_le` |
| `Automata.Complement.complement_state_separation` | `Complement.ufa_unambiguous`, `Complement.ufa_card_le`, `Complement.card_ge_of_complement` (all pre-existing) |
| `Automata.Union.union_state_separation` | `WordCoding.ufa_unambiguous`, `Union.ufa_card_le`, `Union.card_ge_of_union` (all pre-existing) |
| `Automata.Union.union_state_separation_of_unionHard` | `Union.not_hasPartition_of_unionHard` (new) |
| `Automata.ErrorReduction.error_reduction_gap` | `ErrorReduction.anRank_orExtend_le_of_errorHard` (new), `ErrorReduction.ErrorHard.hard` (the structure field) |
| `Arlib.Probability.moment_bounds` | the four projections in §3.6 |

### 6.3 New declarations with no predecessor

Listed so they are not mistaken for renames.

| new fully-qualified name | what |
| --- | --- |
| `Arlib.KnowledgeCompilation.TreeProduct.card_binTree_pathGraph` | `Fintype.card (BinTreeNode r × Fin (2*p)) = (2^(r+1) - 1) * (2*p)` |
| `Arlib.KnowledgeCompilation.TreeProduct.treewidthLe_binTree_pathGraph` | |
| `Arlib.KnowledgeCompilation.TreeProduct.matchingWidthGe_binTree_pathGraph` | side conditions of `binTree_boxProd_matchingWidthGe` discharged |
| `Arlib.KnowledgeCompilation.Asymptotics.maxDegreeLe_razgonGraph` | |
| `Arlib.KnowledgeCompilation.Asymptotics.treewidthLe_razgonGraph` | |
| `Arlib.KnowledgeCompilation.Asymptotics.matchingWidthGe_razgonGraph` | |
| `Arlib.KnowledgeCompilation.Forgetting.bound_le_size_of_computes_sauerhoffFn` | clause (ii) of the capstone, extracted from the structure field `SauerhoffdDNNFLowerBound.hard` |
| `Arlib.KnowledgeCompilation.Forgetting.exists_dDNNF_gFun_size_le` | clause (iii), extracted from `GndDNNFUpperBound.witness` |
| `Arlib.Automata.Union.not_hasPartition_of_unionHard` | the `Gadget.partition κ b` specialisation of the pre-existing `KnowledgeCompilation.Imported.UnionHard.not_hasPartition` |
| `Arlib.Automata.ErrorReduction.anRank_orExtend_le_of_errorHard` | the `1/4` upper half of the error-reduction gap |
| `Arlib.Probability.Ex_centre_sum_sq_eq_varSum` and the three siblings | §3.6 |
| `Arlib.Communication.DependsOnList` and its six lemmas | §5 |
| `Arlib.KnowledgeCompilation.ConicalJunta.IsConical.isConst_of_eq_zero` | degree-0 conical juntas are constants |
| `Arlib.KnowledgeCompilation.ConicalJunta.IsConical.isConst_of_zero` | idem, at literal `0` |
| `Arlib.KnowledgeCompilation.Imported.hardnessOfNegation_witness` | non-vacuity witness for `HardnessOfNegation` |
| `Arlib.KnowledgeCompilation.Imported.nonnegLifting_witness` | non-vacuity witness for `NonnegLifting` |

---

## 7. Known uncertainties, and where the sources disagreed

Recorded rather than resolved, because guessing here would be worse than saying so.

| item | status |
| --- | --- |
| `Arlib.KnowledgeCompilation.Equivalence.traditional_maintheor` → `…traditional_two_rpow_le_size_binTree_pathGraph` | **Corroborated against the tree, but the handoff that covered that directory reports it as *deliberately left alone*.** The rename was applied later in the same branch. The row in §3.1 is the tree's state, which is authoritative. |
| `equivModForget_sauerhoff_gFun` vs `equivModForget_sauerhoffFn_gFun` | The rename audit and the handoff give different spellings, because two renames (`emf`→`equivModForget`, `sauerhoff`→`sauerhoffFn`) apply to the same name. The tree has `equivModForget_sauerhoffFn_gFun`; §3.4 uses that. |
| `Forgetting.sauerhoffdDNNFLowerBound_witness` | The decision list flags it as a follow-on of the `sauerhoff` rename; the agent that applied the rename argued it tracks the *structure* `SauerhoffdDNNFLowerBound`, which is deliberately kept. **It was not renamed.** If the structure is ever renamed, this must follow. |
| `Forgetting.emf_existsFresh` | Referenced from a docstring in `Forgetting/Basic.lean`; **the declaration never existed anywhere in the repository.** The docstring now points at `equivModForget_sauerhoffFn_gFun`, which is a repair based on intent, not on a record. |
| The seven Tseitin non-vacuity witnesses | Left in `Arlib.KnowledgeCompilation.Tseitin`, while the two other areas keep theirs inside `Imported.Nonvacuity`. This is a known inconsistency, not an oversight; moving them would add seven rows here. |
| `Imported.SafeSeparators` | Moved into `Imported` with the other bundles, but its only field is `imported : True`. It carries no statement and is really a provenance marker. |
| `Arlib.KnowledgeCompilation.LowerBounds.ConicalJunta` | A deviation from the brief the module move was given: the file was asked to stay in `KnowledgeCompilation`, and it did, but not in a directory called `Communication/`. Reverting it is one `git mv` plus three import lines. No declaration name is affected either way. |
| `Arlib.Communication.BooleanFunction` | A placement of convenience. `DependsOn` mentions no rectangle, party or partition; it lives here because `Arlib.Communication` is the lowest node of the sub-DAG and is already a dependency of both consumers. If a neutral `Arlib.BooleanFunctions` area is ever created, this module lifts verbatim — a `git mv`, a namespace rename, and an `open` in seven files. |
| Build status | `lake build Arlib` and `lake build ArlibTest` were green after the `Communication` move and after the `FinDist` move. The rename passes in `BranchingPrograms/`, `Tseitin/`, `LowerBounds/`, `Forgetting/`, `Automata/`, `Probability/`, `MDP/` and `Approximation/` were applied without a build; they are textual and type-preserving, but they have not each been independently elaborated. |

---

## 8. Later change: `Arlib.Algorithms` moved to arlib-community

Not part of the `api-overhaul` pass. Recorded here because it is the one change
since that pass which breaks a downstream `import`.

The `Arlib.Algorithms` area — its only sub-area being `TPA/`, Huber's Tootsie Pop
Algorithm — left arlib for the companion repository
[arlib-community](https://github.com/meelgroup/arlib-community). The split it
expresses: arlib is organised by *subject* and holds results stated without
reference to any one algorithm; analyses of *named* algorithms live in
arlib-community, which imports arlib. Nothing in arlib depends on
arlib-community, so the area's departure removes an area root, four modules and
the single `Algorithms → Probability` import edge, and changes nothing else.

Nothing about the mathematics changed. The proofs, statements, hypotheses and
base names are identical; only the module paths and the namespace root moved.

**Add the dependency:**

```toml
[[require]]
name = "arlib-community"
git = "https://github.com/meelgroup/arlib-community.git"
rev = "main"
```

**Then substitute**, on both `import` lines and fully-qualified names:

| old | new |
| --- | --- |
| `Arlib.Algorithms` | `ArlibCommunity.Algorithms` |
| `Arlib.Algorithms.TPA` | `ArlibCommunity.Algorithms.TPA` |
| `Arlib.Algorithms.TPA.Count` | `ArlibCommunity.Algorithms.TPA.Count` |
| `Arlib.Algorithms.TPA.UniformProduct` | `ArlibCommunity.Algorithms.TPA.UniformProduct` |
| `Arlib.Algorithms.TPA.TwoPhase` | `ArlibCommunity.Algorithms.TPA.TwoPhase` |

The first row subsumes the rest: `Arlib.Algorithms` → `ArlibCommunity.Algorithms`
as a prefix substitution is the whole migration. An `open Arlib.Algorithms.TPA`
becomes `open ArlibCommunity.Algorithms.TPA`, and call sites that never spell the
prefix need no edit at all. Declarations of that area still referenced from
arlib's own docstrings: none — `Arlib.Probability.poissonPMF`, which
`UniformProduct.lean` consumes, stays in arlib and is unaffected.
