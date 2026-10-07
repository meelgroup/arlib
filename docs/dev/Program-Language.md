# The arlib Program Language Reference

This document defines the language an arlib program is written in. A program is
the contents of a development's `Model/Program.lean`, or an entry under
`Arlib/Computation/Lib/`.

`docs/dev/Cost-Modelling-Protocol.md` gives the procedure an author follows. This
document says what the result of that procedure may contain.

---

## 1. Introduction

### 1.1 Why the language needs a definition

A cost derived by `Arlib.Computation` describes a program only if the program is
restricted. An unrestricted Lean function of the right type can return the answer
without performing a single charged operation. Its derived cost is then zero, and
every running-time theorem about it holds for an empty reason.

The seals in `Arlib/Computation/` restrict what a program may do with a sealed
value. They do not require the program's data to be a sealed value. Section 1.4
gives three programs that pass every check the repository runs and are outside
the intended language.

This document defines the language by saying what belongs to it. A program is a
Lean term built by the grammar of sections 3 and 4, from the vocabulary of
section 5, meeting the constraints of section 7. A term outside that description
is not a program, whether or not any implemented check rejects it.

### 1.2 The two levels

The language has two levels. They share a grammar and differ in their primitive
operations and their scalar type.

| | Abstract level | Machine level |
| --- | --- | --- |
| Monad | `Charged κ κₛ α` | `RAM w α` |
| Primitives | carrier operations (§5.1) | machine primitives (§5.2) |
| Scalar type | `Num α` | `Word w` |
| Iteration | four combinators (§4.4) | one combinator (§4.4) |
| Where programs live | a development's `Model/Program.lean` | `Arlib/Computation/Lib/` |
| Worked example | `ArlibTest/Computation/AppUnion.lean` | `Arlib/Computation/Lib/Arr.lean` |

A section applies to both levels unless it says otherwise. Examples use the
abstract level.

### 1.3 Notation

The grammar below is written in a modified BNF with these conventions.

A production has the form `name ::= alternative | alternative`. A name in
`lower_case` is a nonterminal. Text in `"quotes"` is a literal Lean identifier or
token. A star means zero or more repetitions of the element before it, a plus
means one or more, and square brackets mean the element is optional. Parentheses
group. Two expressions written next to each other mean Lean function
application, which needs no punctuation. An ellipsis in an example marks omitted
text and is not part of the grammar.

Running text names a syntactic category by writing its production name in code
font.

### 1.4 What is enforced today

No implemented check enforces this document.

The three definitions below elaborate against `Arlib.Computation` as released,
pass `scripts/ComputationAudit.lean` and `scripts/AxiomAudit.lean`, and are not
programs under this document. Test any conformance checker against them before
believing it. Phase 2 of `Cost-Modelling-Protocol.md` requires that every audit be
made to fail on a planted breach.

```lean
-- Not a program: the scrutinee of the conditional is an expression rather than a
-- variable, so nothing was charged for the decision.  Its cost is zero.
def freeBranch (l : List (Fin 8)) : Charged StdOp Cell Bool :=
  if l.length > 3 then pure true else pure false

-- Not a program: `l` has no sort (§2.5), and the value expression computes
-- (§3.2).  Its cost is zero, and `(freeAnswer [0,…,7]).val = 4` is provable by
-- `decide`.
def freeAnswer (l : List (Fin 8)) : Charged StdOp Cell ℕ :=
  pure (l.filter (fun a => a.val % 2 == 0)).length

-- Not a program: the definition is recursive, so no combinator lemma bounds its
-- cost (§7.1).
def loopy : ℕ → Charged StdOp Cell ℕ
  | 0 => pure 0
  | n+1 => do let _ ← Charged.op (.num .add) (); loopy n
```

`scripts/ComputationAudit.lean` passes all three because it lists the constants a
program may not mention, and `List.filter` is not on that list. Section 8
explains why this document lists what a program may mention instead.

---

## 2. Sorts

Every type in a program file belongs to exactly one of four *sorts*, which is
this document's word for a group of types the language treats alike. A
declaration that mentions a type of no sort is not a program.

### 2.1 Carrier types

A *carrier* is one of the sealed structures of `Arlib.Computation`.

```
carrier_type ::= "Roster" type | "Dict" type type | "Heap" type | "Queue" type
               | "Slot" type  | "Num" type       | "Coins" type
               | "Block" index | "Draws" type type | "Sampler"
```

At the machine level the only carrier type is `Word w`.

Each carrier has a private constructor, a private representation field, and a
`noncomputable` view for specifications. A program holds the data of the problem
it solves in a carrier and nowhere else.

### 2.2 Answer types

An *answer* type is one that a charged operation returns. A program may branch on
a value of an answer type.

```
answer_type ::= "Bool" | "Unit" | "ℕ" | carrier_type
              | "Option" answer_type | answer_type "×" answer_type
```

`ℕ` is an answer type because `Roster.size`, `Dict.size` and `Heap.size` return
one. Section 10.2 records this as a deviation and gives the correction.

At the machine level an answer type is `Word w`, `Bool`, `Unit` or `ℕ`.

### 2.3 Index types

An *index* is a shape parameter the analysis quantifies over: the number of
oracle sets, the length of a block, the width of a word. The index types are `ℕ`
and `Fin k` for an index `k`.

An index may appear in a parameter's type and in the range of an iteration
(§4.4). It may not appear in a `value` (§3). The number of oracle sets is a
parameter of the theorem; the contents of those sets are the problem, and they
belong in a carrier.

### 2.4 Program types

A *program type* is `Charged κ κₛ α` for an answer type `α` at the abstract
level, and `RAM w α` at the machine level.

### 2.5 Types of no sort

`List`, `Finset`, `Multiset`, `ℚ`, `ℝ`, function types other than a finite family
of carriers, and every `Prop`-valued type have no sort. A program may not take a
parameter of such a type. A parameter of one of them permits `freeAnswer` in
§1.4.

`List ι` may appear as the range of an iteration, where the `index_list`
production of §4.4 governs it. That is not a parameter.

---

## 3. Values

### 3.1 Value expressions

A `value` is an expression a program may evaluate without charge.

```
value       ::= variable
              | parameter
              | constructor value*
              | projection
              | "Function.update" value value value

projection  ::= value ".1" | value ".2" | value ".val"

variable    ::= an identifier bound by a `let … ←` statement (§4.2), or by a
                binder of an enclosing iteration (§4.4)

parameter   ::= an identifier bound by the enclosing procedure's signature,
                whose type is a carrier type or an index type

constructor ::= a constructor of an answer type (§2.2): "true", "false", "()",
                "none", "some", "Prod.mk", and the anonymous-constructor form
```

`Function.update` is allowed so that a program can replace one member of a finite
family of carriers. `AppUnion.round` uses it to return a queue to its position in
`S₁, …, S_k`.

### 3.2 What a value may not contain

A `value` contains no arithmetic operator, no `decide`, no conditional, no
`match`, no local definition, and no eliminator of a type of no sort (§2.5).

A program produces every quantity by performing a charged operation. A `value`
may name a quantity, pair it with another, select from a pair, or place it in a
family. It may not compute one.

At the machine level the compiler enforces this. `Word w` carries no `Add`, `LT`
or `DecidableEq` instance, so `x + y` and `if x < y then …` do not elaborate. The
abstract level has no equivalent, because its answer types are ordinary Lean
types with their ordinary instances. This section describes what the missing
instances accomplish one level down.

---

## 4. Programs

### 4.1 Program expressions

```
program ::= "pure" value
          | do_block
          | map
          | conditional
          | case_analysis
          | carrier_operation
          | "Charged.op" opcode value
          | iteration
          | procedure_call
```

### 4.2 Sequencing

```
do_block  ::= "do" statement+
statement ::= "let" identifier "←" program        (a binding)
            | program                             (the final statement)
```

The final statement supplies the block's value. Every earlier statement is a
binding, and the identifier it binds is a `variable` in the sense of §3.1
throughout the rest of the block.

A `do_block` denotes a chain of `Charged.bind`. The tally of a bind is the sum of
the tallies of its two parts, so the cost of a sequence needs no rule of its own.

```
map ::= "(" "fun" identifier "=>" value ")" "<$>" program
```

A `map` applies a `value` to a program's answer and charges nothing. See
`Charged.cost_map`.

### 4.3 Selection

```
conditional   ::= "if" variable "then" program "else" program
case_analysis ::= "match" variable "with" alternative+
alternative   ::= "|" pattern "=>" program
```

The scrutinee is a `variable`, not a general `value`. Section 7.2 gives the
reason.

### 4.4 Iteration

```
iteration  ::= "Charged.foldl" step index_list value
             | "Charged.foldlWhile" step index_list value
             | "Num.iterate" round value value
             | "Num.iterateWhile" round value value

step       ::= "(" "fun" identifier identifier "=>" program ")"
round      ::= "(" "fun" identifier identifier "=>" program ")"

index_list ::= "List.finRange" index
             | "List.range" index
             | index_list ".take" value
             | index_list ".drop" value
```

The four combinators differ in two ways.

`Charged.foldl` and `Charged.foldlWhile` run over an `index_list`, whose length
the analysis already knows. `Num.iterate` and `Num.iterateWhile` run a number of
times the program itself computed. That count is held in a `Num ℕ` and never
becomes a value the program can read.

The two `While` forms stop early. Their body returns `none` to stop, and the
tally stops with it.

Each combinator has a cost lemma: `Charged.steps_foldl_le`,
`Charged.steps_foldlWhile_le`, `Num.steps_iterate_le` and
`Num.steps_iterateWhile_le`. `Charged.steps_foldl_ge` gives the matching lower
bound.

The machine level has one combinator, `iterate` of `Arlib/Computation/Loop.lean`,
with `steps_iterate_le` and `steps_iterate_ge`.

### 4.5 Procedure calls

```
procedure_call ::= procedure_name value*
```

A `procedure_name` names a procedure defined earlier in the same file (§6.2). See
§7.1.

---

## 5. The primitive vocabulary

### 5.1 Carrier operations

These are the primitive operations of the abstract level. Each performs one
charged operation, under the opcode the development's `⟨Carrier⟩Ops` instance
supplies.

| Carrier | Operations |
| --- | --- |
| `Roster` | `empty`, `erase`, `insert`, `size`, `cardEq`, `mem`, `filterErase` |
| `Dict` | `empty`, `find`, `insert`, `erase`, `size`, `cardEq` |
| `Heap` | `empty`, `push`, `pop`, `peek`, `size`, `isEmpty` |
| `Queue` | `empty`, `enqueue`, `dequeue`, `isEmpty` |
| `Slot` | `empty`, `isEmpty`, `fill` |
| `Num` | `lit`, `add`, `sub`, `mul`, `div`, `max`, `min`, `le`, `ceil` |
| `Coins` | `flip` |
| `Sampler` | `start`, `accept`, `halve`, `inflate` |
| `Draws` | `pick` |

Two entries are exceptions to the one-charge rule. `empty` and `Sampler.start`
charge nothing and are the only constructors of their carriers.
`Roster.filterErase` charges one `RosterOp.erase` for each element its test
rejects; `Roster.cost_filterErase` reads that count off the pass rather than
taking it from the caller.

A development that performs no operation outside this table declares neither a
currency nor a storage-kind type. `Arlib/Computation/Std.lean` supplies `StdOp`
and `Cell` with the eight naming instances and the four storage instances already
in place. A development that needs an operation with no entry here declares that
operation and its cost, and nothing else.

### 5.2 Machine primitives

The primitives of the machine level are the nineteen `RAM w` functions of
`Arlib/Computation/Machine.lean`:

```
lit  add  sub  mul  mulHi  udiv  umod
band bor  bxor shl  shr    clz
lt   le   eq
load store alloc
```

To these add `emit`, which appends a word to the output log and charges an
`Op.store`, and `loadAt` and `storeAt` of `Arlib/Computation/Data.lean`, which
are the base-plus-index forms.

`Op.randBit` is a constructor of the currency with no primitive behind it. The
randomised machine level is not built.

One primitive charges more than once. `alloc n` charges `n` instances of
`Op.alloc`, so that clearing an allocated region is not free. This is not the
defect §5.3 excludes: a charge counted by data the program holds is an operation,
while a charge counted by a number the author wrote is a cost declaration.

### 5.3 Operations excluded from the language

These belong to `Arlib.Computation` and not to the program language.

**Observers:** `Charged.val`, `Charged.cost`, `Charged.steps`, `Charged.space`,
`Charged.peakAt`, `Charged.netAt`, and at the machine level `Word.toNat`,
`RamState.get`, `RAM.val`, `RAM.state`, `RAM.cost`, `RAM.steps`. A program that
reads its own tally can compute with it. `Roster.cost_filterErase` equates a
pass's tally to a cardinality, so a readable tally is a free cardinality.

**Re-pricing:** `Charged.exchange`. Applying `exchange (fun _ => 0)` discards a
computation's charges. Re-pricing acts on a finished analysis and happens outside
the program.

**Measurement:** `Charged.opUpdate` and `Residency.ofFun`. These assign storage to
a kind. Only a carrier's own operations call them, and each passes its own
module's `private` measure.

**Naming:** every `⟨Carrier⟩Ops.mk` and `⟨Carrier⟩Cells.mk`. A rival instance
files an operation under a name that no bound covers.

**Eliminators:** `casesOn`, `rec` and `recOn` of every sealed type. Lean generates
these public even where the constructor is private, and it compiles `casesOn`.

`Word` is the exception and shows the fix. It is a public alias for a `private`
structure, so the elaborator generates its eliminators under a name that
`private` mangles with `Arlib/Computation/Machine.lean` and no client can write
one. The compiler rejects the field projection, the anonymous-constructor
pattern, `Word.rec` and `Word.casesOn`, and the three `Word` entries are gone
from the audit's list. `Roster` and `Charged` still carry public eliminators.

**Bulk charges:** `Charged.opMany o n a`, which charges `n` operations at once.
The count `n` is a number the author wrote, which rule A2 of
`Cost-Modelling-Protocol.md` forbids in an algorithm's files. `opMany` is for
defining a carrier operation whose single call really does perform several
charged steps. No program in the repository uses it.

The first five groups are the `forbidden` list of
`scripts/ComputationAudit.lean`. They are absent from the grammar, so a checker
built from this document needs no separate list; they appear here for readers of
that script.

---

## 6. Program files

### 6.1 File structure

```
program_file   ::= [ currency ] [ storage_kinds ] naming_instance*
                   [ input_structure ] procedure_definition+

currency       ::= "inductive" identifier … ";" fintype_instance
storage_kinds  ::= "inductive" identifier … ";" fintype_instance
naming_instance::= "instance" ":" ops_class identifier "where" …
                 | "instance" ":" cells_class … "where" …
input_structure::= "structure" identifier … "where" field+
field          ::= identifier ":" (carrier_type | index_type
                                   | index_type "→" carrier_type)
procedure_definition
               ::= "def" procedure_name parameter_binder* ":" program_type
                   ":=" program
```

The first four categories are optional. A development whose operations all come
from §5.1 leaves out `currency`, `storage_kinds` and `naming_instance`, and
writes `StdOp` and `Cell` instead.

### 6.2 Declaration order

Declarations appear in the order the `program_file` production gives. Procedure
definitions appear in dependency order, so a `procedure_call` names a procedure
defined earlier in the same file.

### 6.3 What a program file may not contain

No declaration is marked `noncomputable`. The views a program must not use are
`noncomputable`, so a program that uses one fails to compile; marking a
declaration `noncomputable` turns that mechanism off for the whole declaration.

A parameter whose value is noncomputable, such as a threshold that is the ceiling
of a real number, is passed in as an argument rather than computed. An
implementation is handed its constants.

No declaration is a `theorem`, mentions `CostVec` or a `Rate`, or contains a
numeric literal outside the argument of `Num.lit` or `Charged.op`. Correctness
statements belong to the modelling layer and cost statements to the analysis
layer; see Phases 3 and 4 of `Cost-Modelling-Protocol.md`.

---

## 7. Static constraints

The grammar of sections 3, 4 and 6 cannot express the following five
constraints. A term that satisfies the grammar and breaks any of them is not a
program.

### 7.1 Procedure calls are acyclic

A procedure definition is not recursive, and the call graph of a program file has
no cycle. The combinators of §4.4 are the only iteration.

Each combinator has a cost lemma. A recursive definition has none, so its cost is
a quantity that no bound in the file is stated against.

### 7.2 Every branch was paid for

The scrutinee of a `conditional` or a `case_analysis` (§4.3) is a `variable`
bound by a `let … ←` statement or by an iteration binder.

A `Bool` in a program is the answer to a charged question, and branching on it is
free because the operation that produced it was charged. Branching on a `Bool`
that no operation produced is a decision the program did not pay for.

### 7.3 A value does not compute

A `value` meets §3.2. In particular no `value` contains an arithmetic operator or
an application of `decide`.

### 7.4 A literal takes a name, not an expression

The argument of `Num.lit` is a `parameter` or a `variable`, never a compound
expression. Otherwise `Num.lit (n + 1)` performs a free increment under cover of
a charged operation.

The same holds at the machine level for `lit`, whose natural-number argument must
likewise be a parameter or a variable.

### 7.5 An iteration runs over indices

An `index_list` (§4.4) is built from index-type expressions alone. The length of
an iteration is therefore a quantity the analysis already quantifies over.

### 7.6 A program does not borrow a private name

A program uses a `private` constant only from the module that declared it.

Lean mangles a private name with its module, so a client cannot write it.
Batteries provides `open private a from M in`, which brings the mangled name back
into scope, and the declaration that results is ordinary Lean with no axioms. The
mangled name stays in the elaborated term, so this constraint is checked over the
environment rather than over the source, and `usesForeignPrivate` in
`scripts/ComputationAudit.lean` is the check. It needs no exemption list, because
using a private constant from another module is what `private` already forbids.

---

## 8. Design notes

This section gives reasons. Sections 2 to 7 give the rules.

**Why the document lists what is allowed.** `scripts/ComputationAudit.lean` lists
what is forbidden. Such a list excludes the constructions its author thought of,
and nobody thought of `List.filter`, which is the whole of `freeAnswer` in §1.4.
A list of what is allowed is finite and short enough to read in one sitting, and
it excludes everything else.

**Why §7.2 exists.** Rule A3 of `Cost-Modelling-Protocol.md` says every value an
algorithm touches is a sealed type or an input. It is the only rule in that
document with no mechanical check behind it. Section 7.2 together with §2.5 makes
it checkable. A seal constrains operations on carriers, and cannot constrain a
program that holds no carrier.

**Why both levels share a grammar.** Two of the five constraints in section 7
hold at the machine level with no checker, because `Word w` carries no instances.
Writing both levels against one grammar shows that a checker for the abstract
level reproduces a property the machine level gets from the type system, and
names which property that is.

---

## 9. Checking conformance

Implement §9.2. It costs about 150 lines, it rejects all three definitions of
§1.4, and `docs/dev/Computation-ROADMAP.md` §2.2 already commits to it.

### 9.1 Documentary, which is the current state

This document and `Cost-Modelling-Protocol.md`, with no mechanical check for
sections 2 to 6. All three definitions of §1.4 pass every check the repository
runs.

Two constraints are enforced. Section 7.6 is checked by `usesForeignPrivate` in
`scripts/ComputationAudit.lean`, over `Arlib.Computation` only; a development
runs the same check over its own namespace. Section 3.2 holds at the machine
level because `Word w` carries no instances.

### 9.2 A vocabulary audit

Change `scripts/ComputationAudit.lean` from a list of forbidden constants to a
list of permitted ones, applied to a namespace the development nominates. For
each declaration in that namespace, require every constant in its value to belong
to one of three groups: the vocabulary of sections 4 and 5, the nominated
namespace itself, or a *structural tier*.

The structural tier holds what the elaborator leaves behind: `Bind.bind`,
`Functor.map`, the `Monad` instance, match auxiliaries, `Fin.mk`, `Nat.decEq`,
and the constructors of `Option`, `Prod` and `Bool`.

*Cost.* About 150 lines. The script already walks the environment and already
supports per-declaration exemptions through `areaByPermission`.

*What it catches.* All three definitions of §1.4. `freeAnswer` mentions
`List.filter` and `List.length`, `freeBranch` mentions `List.length` and
`Nat.decLt`, and `loopy` mentions the auxiliary its recursion generates.

*What it misses.* The structural tier is a judgement rather than a consequence of
this document. `Nat.decEq` sits in it, so a comparison of two indices passes,
which is defensible because indices are analysis-level quantities but is a
decision the tier makes rather than one the rules imply. A traversal over
constants cannot see inside a match auxiliary, so it enforces §7.2 through the
constants of the scrutinee rather than through the `match`.

*Standing.* `docs/dev/Computation-ROADMAP.md` §2.2 says the seal's CI should check
"that no declaration mentions a constant outside a whitelist". That half of the
sentence has never been built. The current audit is the other half.

### 9.3 A surface elaborator

Write a `syntax` declaration and a macro that accept only the grammar of sections
3, 4 and 6 and elaborate to the same shallow `Charged` and `RAM` terms.

```lean
algorithm round (I : Input Ω k) (draws : Draws ℕ (Fin k)) (r : ℕ) … :=
  let i ← Draws.pick r draws
  …
```

*Cost.* Between 400 and 800 lines, plus converting every existing program file,
plus maintaining a second surface for `Std.Do` and `mvcgen` to work with.

*What it catches.* All of sections 3, 4 and 6, by construction, and it reports
each violation at the position of the offending construct.

*Standing.* `docs/dev/Computation-ROADMAP.md` §10 counts a surface elaborator
among the four pieces of design risk that the shallow-embedding plan drops.
Building one reverses a recorded decision and should be recorded as one.

Section 10 of that document rejects a *deep* embedding, which is a different
thing: an inductive syntax type, an interpreter, and a compilation theorem. It
gives four grounds — the interpreter needs fuel, the program logic must be
rebuilt, the anti-cheat argument is no stronger than the seal's, and the
compilation theorem is unprecedented. None of the four applies to §9.3, which
produces shallow terms and proves nothing about them. A surface elaborator is a
parser, not a semantics.

Reconsider §9.3 only if the structural tier of §9.2 turns out to be where
non-conforming constructions appear.

---

## 10. Known deviations

The released library breaks this document in two places. Neither blocks §9.2.

### 10.1 An input field of no sort

`ArlibTest/Computation/AppUnion.lean` declares

```lean
structure Input (Ω : Type) [DecidableEq Ω] (k : ℕ) where
  oracle  : Fin k → Roster Ω        -- carrier type
  samples : Fin k → Queue Ω         -- carrier type
  sz      : Fin k → ℚ               -- no sort (§2.5)
```

The field `sz` breaks §6.1. Its documentation states the intended discipline,
that every use of a size goes through `Num.lit` and pays, but the type does not
carry that discipline.

*Correction.* Declare the field `Fin k → Num ℚ`. `Num.mk` is private and
`Num.lit` is the only public way in, so only a program that paid for each
constant can build an `Input`, and the discipline becomes a property of the type.

### 10.2 A size query returning an unsealed natural number

`Roster.size`, `Dict.size` and `Heap.size` charge one operation and return `ℕ`.
The documentation of `Roster.size` calls it the counterpart of `Roster.cardEq`
for a program that needs the number itself.

Section 7.3 limits the damage. The returned `ℕ` is a `variable`, and no `value`
performs arithmetic, so a program can pass it to `Num.lit` or to an iteration
range and do nothing else with it. The deviation is that `ℕ` has to be an answer
type (§2.2) at all.

*Correction.* Let these three operations return `Num ℕ`. No unsealed numeric type
is then an answer type.

---

## Appendix A. Full grammar

This is the abstract level. For the machine level, substitute the vocabulary of
§5.2, the single combinator `iterate`, and `Word w` for `Num α`.

```
program_file   ::= [ currency ] [ storage_kinds ] naming_instance*
                   [ input_structure ] procedure_definition+

currency       ::= "inductive" identifier … ";" fintype_instance
storage_kinds  ::= "inductive" identifier … ";" fintype_instance
naming_instance::= "instance" ":" ops_class identifier "where" …
                 | "instance" ":" cells_class … "where" …
input_structure::= "structure" identifier … "where" field+
field          ::= identifier ":" (carrier_type | index_type
                                   | index_type "→" carrier_type)
procedure_definition
               ::= "def" procedure_name parameter_binder* ":" program_type
                   ":=" program

program        ::= "pure" value
                 | do_block
                 | map
                 | conditional
                 | case_analysis
                 | carrier_operation
                 | "Charged.op" opcode value
                 | iteration
                 | procedure_call

do_block       ::= "do" statement+
statement      ::= "let" identifier "←" program
                 | program
map            ::= "(" "fun" identifier "=>" value ")" "<$>" program
conditional    ::= "if" variable "then" program "else" program
case_analysis  ::= "match" variable "with" alternative+
alternative    ::= "|" pattern "=>" program

iteration      ::= "Charged.foldl"      step  index_list value
                 | "Charged.foldlWhile" step  index_list value
                 | "Num.iterate"        round value      value
                 | "Num.iterateWhile"   round value      value
step           ::= "(" "fun" identifier identifier "=>" program ")"
round          ::= "(" "fun" identifier identifier "=>" program ")"
index_list     ::= "List.finRange" index
                 | "List.range" index
                 | index_list ".take" value
                 | index_list ".drop" value

procedure_call ::= procedure_name value*

value          ::= variable
                 | parameter
                 | constructor value*
                 | projection
                 | "Function.update" value value value
projection     ::= value ".1" | value ".2" | value ".val"

carrier_type   ::= "Roster" type | "Dict" type type | "Heap" type
                 | "Queue" type  | "Slot" type      | "Num" type
                 | "Coins" type  | "Block" index    | "Draws" type type
                 | "Sampler"
answer_type    ::= "Bool" | "Unit" | "ℕ" | carrier_type
                 | "Option" answer_type | answer_type "×" answer_type
index_type     ::= "ℕ" | "Fin" index
program_type   ::= "Charged" identifier identifier answer_type
```

`carrier_operation` ranges over the table in §5.1.

## Appendix B. Excluded identifiers

The identifiers of §5.3, collected for reference.

```
Charged.val        Charged.cost       Charged.steps      Charged.space
Charged.peakAt     Charged.netAt      Charged.exchange   Charged.opUpdate
Charged.opMany     Residency.ofFun
Word.toNat         RamState.get       RAM.val            RAM.state
RAM.cost           RAM.steps
RosterOps.mk       DictOps.mk         HeapOps.mk         QueueOps.mk
RandOps.mk         DrawOps.mk         SlotOps.mk         NumOps.mk
RosterCells.mk     DictCells.mk       HeapCells.mk       QueueCells.mk
⟨sealed type⟩.casesOn   ⟨sealed type⟩.rec   ⟨sealed type⟩.recOn
```
