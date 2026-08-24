# References

Every paper the library formalizes or cites, with the short key used in the Lean
docstrings. A citation in the source looks like ``[Raz16, Lemma 12]`` or
``[VS24, `thm: main`]``: a key from this file, plus the paper's own theorem
number or LaTeX label.

**Why keys and not paths.** These citations used to point at files under a local
`source/` directory, by path and line number. That directory is not distributed —
it holds third-party papers whose redistribution is not ours to decide — so those
citations were unresolvable for every reader who was not the original author, and
they broke whenever a paper was re-downloaded. A theorem number survives both.

Where a citation carries the paper's own LaTeX label (`thm: main`,
`lemma:1BP_are_well_structured`), that label is deliberate: it is how a reader
working through the source locates the statement, and it is stable in a way line
numbers are not.

## Primary sources

The papers whose results are formalized here at length. Each is the subject of an
area or a subdirectory, and the corresponding area root says what was formalized
and what was deliberately left out.

**`CSV23`** — Zongchen Chen, Daniel Štefankovič, Eric Vigoda.
*Spectral Independence and Local-to-Global Techniques for Optimal Mixing of Markov Chains.*
arXiv:2307.13826 (2023). Monograph / lecture-note style survey.

**`VS24`** — Harry Vinall-Smeeth.
*Structured d-DNNF Is Not Closed Under Negation.*
Proceedings of the 33rd International Joint Conference on Artificial Intelligence (IJCAI 2024).
arXiv:2403.03362.

**`Raz16`** — Igor Razgon.
*On the Read-Once Property of Branching Programs and CNFs of Bounded Treewidth.*
Algorithmica 75(2):277–294, 2016. DOI 10.1007/s00453-015-0059-x.

**`GKY22`** — Mika Göös, Stefan Kiefer, Weiqiang Yuan.
*Lower Bounds for Unambiguous Automata via Communication Complexity.*
49th International Colloquium on Automata, Languages, and Programming (ICALP 2022),
LIPIcs vol. 229, pp. 126:1–126:13. DOI 10.4230/LIPIcs.ICALP.2022.126. arXiv:2109.09155.

**`OD17`** — Umut Oztok, Adnan Darwiche.
*On Compiling DNNFs without Determinism.*
CoRR abs/1709.07092 (2017). arXiv:1709.07092.

**`OD14`** — Umut Oztok, Adnan Darwiche.
*On Compiling CNF into Decision-DNNF.*
Principles and Practice of Constraint Programming (CP 2014), LNCS 8656, pp. 42–57. Springer, 2014.
DOI 10.1007/978-3-319-10428-7_7.

**`dCM21`** — Alexis de Colnet, Stefan Mengel.
*Characterizing Tseitin-Formulas with Short Regular Resolution Refutations.*
24th International Conference on Theory and Applications of Satisfiability Testing (SAT 2021),
LNCS 12831, pp. 116–133. Springer, 2021. arXiv:2103.09609.
Journal version: JAIR 76 (2023).

**`CP15`** — Michael B. Cohen, Richard Peng.
*ℓp Row Sampling by Lewis Weights.*
47th ACM Symposium on Theory of Computing (STOC 2015), pp. 183–192. DOI 10.1145/2746539.2746567.
arXiv:1412.0588.
## Secondary sources

Works cited in passing: results imported as hypotheses, standard references for a
technique, and the original sources of classical facts.

Knowledge-compilation / communication-complexity cluster:

**`BBGJK21`** — Kaspars Balodis, Shalev Ben-David, Mika Göös, Siddhartha Jain, Robin Kothari.
*Unambiguous DNFs and Alon–Saks–Seymour.* 62nd IEEE FOCS, 2021. arXiv:2102.08348.
(From `source/kc/goos/ufa_main.tex` bibliography, `Balodis2021FOCS`.)

**`GLMWZ16`** — Mika Göös, Shachar Lovett, Raghu Meka, Thomas Watson, David Zuckerman.
*Rectangles Are Nonnegative Juntas.* SIAM J. Comput. 45(5):1835–1869, 2016. DOI 10.1137/15M103145X.

**`GJPW18`** — Mika Göös, T. S. Jayram, Toniann Pitassi, Thomas Watson.
*Randomized Communication versus Partition Number.* ACM Trans. Comput. Theory 10(1):1–20, 2018.
DOI 10.1145/3170711.

**`KMR21`** — Pravesh Kothari, Raghu Meka, Prasad Raghavendra.
*Approximating Rectangles by Juntas and Weakly Exponential Lower Bounds for LP Relaxations of CSPs.*
SIAM J. Comput. (STOC'17 special section) pp. STOC17-305–STOC17-332, 2021. DOI 10.1137/17M1152966.
Preliminary version STOC 2017. (Cited in Lean as "Kothari21" / "Kothari".)

**`Goo15`** — Mika Göös. *Lower Bounds for Clique vs. Independent Set.*
56th IEEE FOCS, pp. 1066–1076, 2015. DOI 10.1109/FOCS.2015.69.
(Its Theorem 4 is the non-deterministic lifting theorem imported by `Arlib/Automata/Imported.lean`.)

**`KN97`** — Eyal Kushilevitz, Noam Nisan. *Communication Complexity.* Cambridge University Press, 1997.
(Example 2.12 is the full-rank fact for the `k`-uniform disjointness matrix; also the source of the
protocol characterisation of `NCC`/`UCC`.)

**`Raz90`** — Alexander Razborov. *Applications of Matrix Methods to the Theory of Lower Bounds in
Computational Complexity.* Combinatorica 10(1):81–93, 1990. DOI 10.1007/BF02122698.
(The covering-set lemma in `Arlib/Automata/Disjointness.lean`.)

**`Got66`** — D. H. Gottlieb. *A Certain Class of Incidence Matrices.* Proc. AMS 17:1233–1237, 1966.

**`WC81`** — Mark N. Wegman, J. Lawrence Carter. *New Hash Functions and Their Use in Authentication
and Set Equality.* J. Comput. Syst. Sci. 22(3):265–279, 1981.
(Confirmed: `source/kc/arXiv.bbl:202–205`; `lem: indperm` at `arXiv.tex:423` cites `wegman1981new`.)

**`Kno17`** — Alexander Knop. *IPS-like Proof Systems Based on Binary Decision Diagrams.*
Electron. Colloq. Comput. Complex. TR17-179, 2017.
(Confirmed: `source/kc/arXiv.bbl:130–133`; `VS24`'s Claim `perm` cites its Theorem 4.2.)

**`PD08`** — Knot Pipatsrisawat, Adnan Darwiche. *New Compilation Languages Based on Structured
Decomposability.* AAAI 2008, pp. 517–522. (Source of structured d-DNNF and of the rectangle lemma.)

**`Dar11`** — Adnan Darwiche. *SDD: A New Canonical Representation of Propositional Knowledge Bases.*
IJCAI 2011, pp. 819–826. (Source of SDD and of the polynomial-time complementation fact, imported
as `Imported.SDDComplementation`.)

**`BCMS16`** — Simone Bova, Florent Capelli, Stefan Mengel, Friedrich Slivovsky.
*Knowledge Compilation Meets Communication Complexity.* IJCAI 2016, pp. 1008–1014.
(Both the rectangle lemma and the d-DNNF lower bound for the Sauerhoff function, and the
rectangle-cover game that `Tseitin/RectangleGame.lean` refines.)

**`Sau03`** — Martin Sauerhoff. *Approximation of Boolean Functions by Combinatorial Rectangles.*
Theoret. Comput. Sci. 301(1–3):45–78, 2003.
(The function `f_n = row_n ∨ col_n` in `Forgetting/Separation.lean`.)

**`BLRS13`** — Paul Beame, Jerry Li, Sudeepa Roy, Dan Suciu. *Lower Bounds for Exact Model Counting
and Applications in Probabilistic Databases.* UAI 2013.

**`HW17`** — Daniel J. Harvey, David R. Wood. *Parameters Tied to Treewidth.*
J. Graph Theory 84(4):364–385, 2017. (`Tseitin/Branchwidth.lean`'s `HarveyWood`; `dCM21`'s Lemma 2
cites it as `[HW17, Lemma 12]` — `source/kc/decolnet/main.bib:392–400`.)

**`AR11`** — Michael Alekhnovich, Alexander A. Razborov. *Satisfiability, Branch-Width and Tseitin
Tautologies.* Comput. Complex. 20(4):649–678, 2011.
(`Tseitin/Main.lean`'s `AlekhnovichR11` bundle — `source/kc/decolnet/main.bib:33–41`.)

**`IRSS19`** — Dmitry Itsykson, Artur Riazanov, Danil Sagunov, Petr Smirnov.
*Near-Optimal Lower Bounds on Regular Resolution Refutations of Tseitin Formulas for
Graphs of Bounded Carving Width.* Algorithmica 83:2170–2200, 2021; conference version
SAT 2020. (Cited in `Tseitin/{Search,ThreeConnected}.lean` as the source of the
minimal-size 1-BP / well-structuredness results. **Identification is from content
alone** — the key appeared in the docstrings without a bibliography entry.)

**`LNNW95`** — László Lovász, Moni Naor, Ilan Newman, Avi Wigderson. *Search Problems in the Decision
Tree Model.* SIAM J. Discrete Math. 8(1):119–132, 1995.
(`Tseitin/Search.lean`'s `LovaszNNW` — `source/kc/decolnet/main.bib:812–822`.)

**`dCM21b`** — Alexis de Colnet, Stefan Mengel. *A Compilation of Succinctness Results for Arithmetic
Circuits.* 18th Int. Conf. on Principles of Knowledge Representation and Reasoning (KR 2021),
pp. 205–215.
⚠️ **DO NOT CONFLATE WITH `dCM21`.** The "de Colnet–Mengel Proposition 2 / Lemma 10" cited in
`Circuits/Arithmetic.lean`, `LowerBounds/Arithmetic.lean` and `LowerBounds/Imported.lean` (imports
I4 and I6 of the KC roadmap) are from **this** arithmetic-circuit paper, *not* from the Tseitin paper
whose `.tex` sits in `source/kc/decolnet/`. Confirmed: `source/kc/arXiv.bbl:87–94`
(`DBLP:conf/kr/ColnetM21`) is what `VS24` cites at its `lem: AC`.

Markov-chain cluster:

**`CLV21`** — Zongchen Chen, Kuikui Liu, Eric Vigoda. *Optimal Mixing of Glauber Dynamics: Entropy
Factorization via High-Dimensional Expanders.* STOC 2021. arXiv:2011.02075.

**`AJKPV`** — Nima Anari, Vishesh Jain, Frederic Koehler, Huy Tuan Pham, Thuy-Duong Vuong.

**`Hub06`** — Mark Huber. *Fast Perfect Sampling from Linear Extensions.*
Discrete Mathematics 306(4):420–428, 2006. DOI 10.1016/j.disc.2006.01.003.
(Cited in full — the fullest citation in the whole repo — at
`Techniques/SinusoidalPotential.lean:26–28`, as "Huber 2006b, Theorem 5".)

**`Wil04`** — David B. Wilson. *Mixing Times of Lozenge Tiling and Card Shuffling Markov Chains.*
Ann. Appl. Probab. 14(1):274–325, 2004. arXiv:math/0102193.

**`KK91`** — Alexander V. Karzanov, Leonid G. Khachiyan. *On the Conductance of Order Markov Chains.*
Order 8(1):7–15, 1991. Confidence: **high** (named only as "the Karzanov–Khachiyan chain").

**`DS87`** — Persi Diaconis, Mehrdad Shahshahani. *Time to Reach Stationarity in the Bernoulli–Laplace
Diffusion Model.* SIAM J. Math. Anal. 18(1):208–218, 1987.
Probability cluster:

**`Fre75`** — David A. Freedman. *On Tail Probabilities for Martingales.*
Ann. Probab. 3(1):100–118, 1975. DOI 10.1214/aop/1176996452. (`Probability/Freedman.lean`.)

**`RS71`** — Herbert Robbins, David Siegmund. *A Convergence Theorem for Non Negative Almost
Supermartingales and Some Applications.* In *Optimizing Methods in Statistics* (J. S. Rustagi, ed.),
Academic Press, 1971, pp. 233–257. (`Probability/StochasticApproximation.lean`, `Probability.lean`.)

**`RM51`** — Herbert Robbins, Sutton Monro. *A Stochastic Approximation Method.*
Ann. Math. Statist. 22(3):400–407, 1951. DOI 10.1214/aoms/1177729586.
(`Probability/RobbinsMonro.lean`, `Probability/CondExpFreshDraw.lean`, `MDP/EndComponent.lean`.)

**`BR94`** — Mihir Bellare, John Rompel. *Randomness-Efficient Oblivious Sampling.*
35th IEEE FOCS, pp. 276–287, 1994. DOI 10.1109/SFCS.1994.365687. (`Probability/KWiseChernoff.lean`.)

**`SSS95`** — Jeanette P. Schmidt, Alan Siegel, Aravind Srinivasan. *Chernoff–Hoeffding Bounds for
Applications with Limited Independence.* SIAM J. Discrete Math. 8(2):223–250, 1995
(prelim. SODA 1993). DOI 10.1137/S089548019223872X.
(`KWiseChernoff`, `StirlingMoment`, `MomentToTail`, `MomentMethod`, `EvenMoment`.)

**`BGHP`** — Jacqueline Banks, Scott Garrabrant, Mark L. Huber, Anne Perizzolo.
*Using TPA to Count Linear Extensions.* arXiv:1010.4981; J. Discrete Algorithms (2018).
(`Probability/Poisson.lean`, Lemmas 2 and 3 — plus a recorded **correction** to the published proof
of the lower tail.)

**`Lev37`** — Paul Lévy's conditional extension of Borel–Cantelli. Modern reference:
D. Williams, *Probability with Martingales*, CUP 1991, Theorem 12.15.

**`MCM24`** — Kuldeep S. Meel ⓡ Sourav Chakraborty ⓡ Umang Mathur. *A Faster FPRAS for #NFA.*
PODS 2024. arXiv:2312.13320. DOI 10.1145/3651588.
(`Probability/LevelCoupling.lean` — explicit; `CouplingFinProb.lean` and `CondEvent.lean` say only
"the `#NFA` FPRAS of PODS 2024".)

**`ACJR21`** — Marcelo Arenas, Luis Alberto Croquevielle, Rajesh Jayaram, Cristian Riveros.
*#NFA Admits an FPRAS: Efficient Enumeration, Counting, and Uniform Generation for Logspace Classes.*
J. ACM 68(6), art. 48, 2021 (STOC 2021). arXiv:1906.09226.
Companion for the tree-automata/CQ statements: *When Is Approximate Counting for Conjunctive Queries
Tractable?*, STOC 2021, arXiv:2005.10029.

**`TATA`** — H. Comon, M. Dauchet, R. Gilleron, C. Löding, F. Jacquemard, D. Lugiez, S. Tison,
M. Tommasi. *Tree Automata Techniques and Applications.* Online book, release 2007.
(Cited via the source paper's `lem-tata` in `Automata/TreeAutomatonBinarize.lean` and
`TreeAutomatonOps.lean`.)

Approximation / algorithms cluster:

**`KL83`** — Richard M. Karp, Michael Luby. *Monte-Carlo Algorithms for Enumeration and Reliability
Problems.* 24th IEEE FOCS, pp. 56–64, 1983.

**`KLM89`** — Richard M. Karp, Michael Luby, Neal Madras. *Monte-Carlo Approximation Algorithms for
Enumeration Problems.* J. Algorithms 10(3):429–448, 1989.
(`Approximation/KarpLuby*.lean`, `Automata/SuccinctNFA.lean`. Cite KLM89 for the estimator as used.)

**`Hoe63`** — Wassily Hoeffding. *Probability Inequalities for Sums of Bounded Random Variables.*
J. Amer. Statist. Assoc. 58(301):13–30, 1963.

**`JVV86`** — Mark R. Jerrum, Leslie G. Valiant, Vijay V. Vazirani. *Random Generation of
Combinatorial Structures from a Uniform Distribution.* Theoret. Comput. Sci. 43:169–188, 1986.
(`Approximation/SelfReducible.lean`; also the folklore median amplification in `Amplification.lean`.)

**`Gore97`** — Vivek Gore, Mark Jerrum, Sampath Kannan, Z. Sweedyk, Steve Mahaney. *A Quasi-Polynomial-
Time Algorithm for Sampling Words from a Context-Free Language.* Inform. and Comput. 134(1):59–74, 1997.

**`Lew78`** — D. R. Lewis. *Finite Dimensional Subspaces of `L_p`.* Studia Math. 63:207–212, 1978.
(The weights themselves.)

**`Khi23`** — A. Khintchine. *Über dyadische Brüche.* Math. Z. 18:109–116, 1923.

**`LT91`** — Michel Ledoux, Michel Talagrand. *Probability in Banach Spaces: Isoperimetry and
Processes.* Springer, Ergebnisse 23, 1991. (Contraction principle, Thm 4.12; symmetrization §6.1.)

**`Tal90`** — Michel Talagrand. *Embedding Subspaces of `L_1` into `ℓ_1^N`.* Proc. AMS 108:363–369, 1990.
(The iterative `¾n`-halving that would give `log n → log d`.)

**`Ban22`** — Stefan Banach. *Sur les opérations dans les ensembles abstraits…* Fund. Math. 3:133–181, 1922.

**`Tro12`** — Joel A. Tropp. *User-Friendly Tail Bounds for Sums of Random Matrices.*
Found. Comput. Math. 12:389–434, 2012. arXiv:1004.4389. (Cited only *by exclusion*: "no matrix Chernoff".)

Game theory / MDP:

**`Yao77`** — Andrew Chi-Chih Yao. *Probabilistic Computations: Toward a Unified Measure of
Complexity.* 18th IEEE FOCS, pp. 222–227, 1977. DOI 10.1109/SFCS.1977.24.
(`GameTheory/YaoMinimax.lean`.)

**`vN28`** — John von Neumann. *Zur Theorie der Gesellschaftsspiele.* Math. Ann. 100:295–320, 1928.
(Named in `YaoMinimax.lean` as the theorem *not* needed.)

**`Bel57`** — Richard Bellman. *Dynamic Programming.* Princeton University Press, 1957.

**`Put94`** — Martin L. Puterman. *Markov Decision Processes: Discrete Stochastic Dynamic
Programming.* Wiley, 1994. (`Arlib/MDP/**` — but see **Known gaps** below: the MDP area quotes an
unnamed source paper verbatim, and this textbook is not it.)

Classical named results used without attribution (report only; probably need no key):
Cheeger's inequality (easy direction), Pinsker's inequality (sharp constant 2 — Csiszár/Kullback/
Kemperman 1967–69), Metropolis–Hastings (1953/1970), Kullback–Leibler (1951), Gibbs' inequality,
Han's inequality (Han 1978, named explicitly in `Chains/ProductEntropy.lean`), Jensen, Young/Fenchel,
Jordan's inequality, Chernoff (1952), Markov, Chebyshev, Stirling, Fano, coupon collector.

---
## Unattributed — known gaps

The following citations are **missing**, and that is a defect in the library
rather than a neutral fact about it. Each one is a place where the source could
not be recovered from the repository: a docstring quotes a result, sometimes
verbatim and by theorem number, without saying whose result it is. Formalized
mathematics that cannot be traced back to its source is harder to check and
harder to credit, and in one case below (`Arlib/MDP/**`) that gap covers an
entire area.

They are listed rather than guessed because a plausible-looking wrong citation is
worse than an acknowledged missing one — it survives review. But listing them is
not a fix. Each needs an answer from the author, and until it has one the
corresponding docstrings say the source is unknown instead of naming a paper.

| Where | What is cited | What is known |
| --- | --- | --- |
| `Arlib/MDP/**` | A specific paper, quoted verbatim and by pseudocode line number (`Bellman.lean`, `Basic.lean`, `Reachability.lean`, `FixedPoint.lean`). | Never named anywhere in the repository. Reads as a Q-learning-for-reachability paper. |
| `Arlib/Probability/TVDistance.lean` | LaTeX labels `lem:dtv`, `lem:condtv`, `lem:averagingtv` in an unshipped `prelims.tex` / `extended-prelims.tex`. | Copyright names Uddalok Sarkar; likely an in-preparation paper. Same for `IntersectionTailBound.lean`. |
| `Arlib/Approximation/KarpLubyApprox.lean` | "Gore et al." | No in-repo anchor; the attribution is deferred to a file in a different repository. `Gore97` below is an identification from content alone. |
| `Arlib/MarkovChains/**` | `relax-optimal` — Anari, Jain, Koehler, Pham, Vuong. | The result cited is "optimal relaxation time of the Glauber dynamics implies spectral independence" (`CSV23`, `lem:opt-relax-SI`). The monograph's own bibliography is not distributed, so the exact paper is unconfirmed. |
| `Arlib/MarkovChains/**` | `CLV21` — Chen, Liu, Vigoda, located only as "Fact A.8" / "Theorem A.9". | Best candidate arXiv:2011.02075 (STOC 2021); two same-author papers of the period are plausible. |
| `Arlib/Automata/SuccinctNFA*`, `TreeAutomaton*` | An unshipped bundle (`fpras2.tex`, `partition-size2.tex`, `sketch.tex`). | Arenas–Croquevielle–Jayaram–Riveros; possibly a journal superset of the `#NFA` FPRAS (arXiv:1906.09226) and the tree-automata paper (arXiv:2005.10029). |

Two more surfaced during the citation pass and are equally unresolved:
`Arlib/Probability/StochasticApproximation.lean` carries a label
`lem:tsitsiklis` with no source anywhere in the repository (it reads as the same
unnamed paper the MDP area quotes), and `Arlib/MarkovChains/Techniques/Mixture.lean`
attributes a positive-semidefiniteness fact to Dyer–Greenhill–Ullrich without a
citation, locating it only by a line number in the undistributed monograph.

Two further identifications are standard but were not checked against the paper
itself: `Got66` (named without a citation in `Automata/Disjointness.lean`) and the
venue for `BLRS13` (UAI 2013 versus the extended ACM TODS 2017 version).
