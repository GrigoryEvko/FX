# Maranget Pattern Matching — FX Specification

Status: spec for N-series (N1–N12).  Maps Maranget 2008 "Compiling
Pattern Matching to Good Decision Trees" onto FX's `match` elaborator,
replacing the Q81–Q86 ad-hoc cascade.

Reference: Luc Maranget, "Compiling Pattern Matching to Good Decision
Trees", ML '08.  https://dl.acm.org/doi/10.1145/1411304.1411311

Scope of this doc: the algorithm FX implements, the data types the
implementation uses, the soundness properties we claim, and the
diagnostics we emit.  The code in `FX/Elab/Maranget.lean` conforms
to this spec; divergences are bugs or policy-flagged deviations
noted inline.


## 1. Why Maranget

The prior `elabMatch` implementation grew bottom-up through Q81–Q86:
wildcards, var-pattern catch-alls, guards, `as`-patterns, nested
ctor destructuring, or-patterns.  Each feature added its own
special case to `buildMethods`.  The composition is fragile —
Q85+Q86 silently drops arms when an or-pattern introduces multiple
ctor-specific arms for the same outer ctor (see §27.2 of
`fx_design.md`; the counterexample case is documented in the
MetatheoryCorpus entry for Q85/Q86).

Maranget's algorithm handles all of:

  * Wildcards, variable bindings, constructor patterns, nested
    constructors, or-patterns, `as`-patterns, guards.
  * Exhaustiveness checking (reports missing patterns).
  * Useless-clause detection (reports unreachable arms).

...as **one uniform decision-tree construction** with a published
soundness proof.  The compositional interaction bugs that Q81–Q86
produces are structurally impossible: the algorithm cannot drop an
arm silently, because every row contributes either to a branch in
the decision tree or to the useless-clause report.

FX's commitment: match elaboration is ONE call through
`Maranget.compile`, not a cascade of per-feature passes.


## 2. Data types

```
/-- One row in the clause matrix.  A row represents one source arm
    (expanded: or-patterns produce multiple rows with the same
    `armIdx`, so useless-clause reporting still attributes back to
    the right source line). -/
structure Row where
  patterns : Array Ast.Pattern  -- pattern vector, one per column
  guard    : Option Ast.Expr     -- arm's guard expression, if any
  body     : Ast.Expr             -- arm's body
  armIdx   : Nat                 -- source arm index, stable across
                                 --   or-pattern expansion
  asBinds  : Array (Nat × String) -- (column, name) from `as` on
                                 --   this row's patterns
  span     : Span

/-- A clause matrix is an ordered list of rows.  The columns
    correspond to the scrutinee vector — at the top level a match
    on a single expression has one column. -/
abbrev ClauseMatrix : Type := Array Row

/-- Decision tree.  `Switch col` inspects the column-indexed
    scrutinee and dispatches per ctor; `Leaf` emits a body (with
    guard handling), `Fail` signals an uncovered pattern space. -/
inductive DecisionTree where
  | Leaf   (body : Ast.Expr) (guard : Option Ast.Expr)
           (asBinds : Array (Nat × String))
           (fallthrough : DecisionTree)  -- taken when guard fails
  | Switch (col : Nat) (branches : Array (IndCtor × DecisionTree))
           (default : Option DecisionTree)
  | Fail   (witness : Array Ast.Pattern)  -- counter-example pattern
                                          -- vector for diagnostics
```

Each field is load-bearing:

  * `armIdx` survives or-pattern expansion so diagnostics point at
    the source arm, not a synthetic row.
  * `asBinds` defers `as`-binding insertion to leaf elaboration,
    where the scrutinee path is known (so we can emit the correct
    β-redex to materialise the named value; composes with Q82/Q84
    at the kernel layer).
  * `fallthrough` on Leaf is how guards compose: if the guard
    fails at runtime, dispatch falls through to the decision tree
    built from the rest of the matrix.  This is Maranget's
    natural guard handling — no separate Q83-like wrapper.
  * `witness` on Fail carries the specific pattern the algorithm
    proved was not covered; the diagnostic renders it as the
    missing-case example.


## 3. The algorithm

### 3.1 Specialization S(c, P)

Given a ctor `c` of arity `k` and a matrix `P`, produce a new
matrix by processing each row's column 0:

  * If column 0 is `c(p_1, ..., p_k)` — replace with
    `p_1, ..., p_k` prepended to columns 1..n.  Row survives.
  * If column 0 is `c'(_)` where `c' ≠ c` — row dropped
    (doesn't match).
  * If column 0 is `_` or `v` (wildcard/variable) — replace with
    `_, _, ..., _` (k wildcards) prepended.  Row survives.
  * Or-patterns and as-patterns at column 0 must have been
    expanded/stripped before S runs (§3.4, §3.5).

### 3.2 Default D(P)

Produce a matrix with rows whose column 0 is `_` or `v`, columns
1..n retained.  All other rows dropped.  Used to compute the
"default branch" of a Switch — the tree walked when the scrutinee
is not any of the explicit ctors covered by specializations.

### 3.3 Compile(P : ClauseMatrix) → DecisionTree

Core recursion:

  1. If `P` is empty → `Fail witness=[_]` — no arm matches anything.
  2. If `P.head.patterns` is all wildcards/vars → `Leaf` with the
     head row's body + guard + asBinds, fallthrough computed from
     `Compile(P.tail)` if the head has a guard (if no guard,
     fallthrough is a `Fail` — the leaf unconditionally matches
     and subsequent rows are unreachable).
  3. Otherwise pick a column `j` to split on.  FX uses leftmost
     column with a non-wildcard row at the top (Maranget's simple
     heuristic; "needed column" heuristics are future work).
  4. Let `Σ = {ctors appearing in column j}`.  For each `c ∈ Σ`:
     recurse on `S(c, P)` to produce a branch for `c`.
  5. If `Σ` covers the spec's full ctor set (a "complete signature"
     per Maranget §3) → no default branch needed.  Else recurse on
     `D(P)` to produce the default.
  6. Emit `Switch col=j branches=... default=...`.

### 3.4 Or-pattern expansion (pre-pass)

Before Compile runs, every row with an or-pattern
`p_1 | p_2 | ... | p_k` at any column is expanded into k rows,
each with one alternative at that column.  Row order is preserved
(alternatives in source order, followed by subsequent rows).
All expanded rows share the same `armIdx`, `body`, `guard`, and
`span`.  This means:

  * `Zero | Succ(Zero) | Succ(Succ(Zero)) => True` produces three
    rows that ALL route to the same body, and the algorithm
    covers each specialized ctor branch correctly.
  * Useless-clause detection operates on the ORIGINAL arm count
    (via `armIdx`): if ALL expanded rows from one source arm are
    unreachable, that source arm is reported as dead.  If only
    SOME are unreachable, the arm still counts as live (at least
    one alternative reached).

### 3.5 As-pattern stripping (pre-pass)

Before Compile runs, every `pat as name` pattern in a row is
stripped to `pat`, and `(column, name)` appended to the row's
`asBinds`.  At Leaf emission the runtime materializes the named
value via the same β-redex mechanism Q82/Q84 used (but now
uniformly applied).

### 3.6 Guard handling

Guards live on Leaf only (by construction: a guard attaches to a
specific row's body, not to a Switch node).  When Compile hits a
Leaf candidate with a guard:

  * Build a DecisionTree for `P.tail` (the matrix with the head
    row removed).  This is the `fallthrough` — where execution
    goes if the guard is false.
  * Emit `Leaf body guard asBinds fallthrough`.

At kernel-lowering time (N10) the Leaf emits:

```
if guard then body else fallthrough_lowered
```

which is structurally identical to Q83's if-chain but applies
uniformly because every Leaf has the same shape.

### 3.7 Useless-clause detection — `useful(P, q)`

Per Maranget §3.1: `useful(P, q) : Bool` — is there a value
matched by `q` but not by any row of `P`?

```
useful(∅, q)      = True   — no rows, anything is useful
useful(P, (c(p̄), ...))
                   = useful(S(c, P), (p̄, ...))
useful(P, (_, ...))
                   = useful(D(P), (...))   if Σ(P) is incomplete
                   = ∨_{c ∈ spec ctors} useful(S(c, P), (wildcards_c, ...))
                                       otherwise
```

The recursion mirrors Compile's.  Uses:

  * **Exhaustiveness**: `useful(fullMatrix, (_, _, ..., _))` — if
    true, the wildcard vector is a missing pattern, emit E010 with
    the witness rendered as a pattern example.
  * **Useless clause**: for each arm index `i > 0`, check
    `useful(rows[0..i-1], rows[i].pattern)` — if false, arm `i`
    is unreachable; emit W001-like diagnostic tied to `armIdx[i]`.
    If an or-pattern produced multiple rows for the same arm, the
    arm is useless iff ALL its rows are useless.


## 4. Lowering to kernel

At the kernel level a DecisionTree becomes a `Term` built from
`Term.indRec` applications nested per Switch depth, with Leaf
bodies elaborated under scopes appropriate for their column
projections:

  * `Switch col branches default` at scrutinee `s` lowers to
    `Term.indRec specName motive methods scrutinee`, where
    `methods[c]` is the lowered branch for ctor `c` (with ctor
    args bound in scope for the recursion), and `default` (if
    present) is merged into the methods whose ctor isn't
    explicitly branched.
  * `Leaf body guard asBinds fallthrough` elaborates `body` in
    the current scope (extended with `asBinds`), wraps in
    `if guard then body' else fallthrough_lowered` via
    `Term.indRec "Bool"` when `guard.isSome`.
  * `Fail witness` at a reachable site is a compile error E010
    (non-exhaustive); at an unreachable site (beyond a Leaf
    without a guard) it is silently elided.

The lowering is deterministic and total — the tree structure
dictates the kernel term.


## 5. Diagnostics

### E010 — non-exhaustive match

Emitted when `useful(P, (_, ..., _))` returns true.  The witness
is rendered as a surface-syntax pattern example.  Example:

```
error[E010]: non-exhaustive match at foo.fx:12:3 — no arm covers
  List(Nat).Cons(_, List(Nat).Cons(_, _))
  suggestion: add an arm handling the two-or-more-element case,
              or a wildcard catch-all `_ => …`.
```

### W001 — unreachable match arm

Emitted when a source arm's patterns are all subsumed by earlier
arms.  Example:

```
warning[W001]: unreachable arm at foo.fx:14:3 — already covered
  by the arm at foo.fx:12:3
  pattern: Succ(Succ(Zero))
  suggestion: remove this arm, or reorder so its case is
              reachable.
```

Release mode treats W001 as an error per §10.12.


## 6. Soundness properties

Per Maranget §2.4–§3.3 (restated as FX invariants):

  * **Compile respects source semantics**: for any value `v` and
    any matrix `P`, the Compile(P) decision tree accepts `v` iff
    some row of `P` accepts `v`, and routes to the body of the
    FIRST such row.
  * **Exhaustiveness is sound and complete**: `useful(P, (_, …))`
    is true iff there exists a value accepted by no row of `P`.
  * **Useless-clause is sound**: if `useful(P[0..i-1], P[i].pat)`
    is false, then arm `i` is never selected at runtime.

The FX implementation doesn't prove these in Lean 4 yet; they are
asserted from Maranget 2008 and from the Rust/OCaml implementation
corpus.  Mechanized proofs are a future task under the R-series
metatheory track.


## 7. What Maranget retires

The following Q-series elaboration surface tasks become obsolete
once N-series is complete:

  * Q81 — wildcard arm catch-all — subsumed by D(P).
  * Q82 — variable-pattern catch-all — subsumed by D(P) +
    as-binding mechanism.
  * Q83 — match-arm guards — subsumed by Leaf fallthrough.
  * Q84 — as-patterns — subsumed by pre-pass as-stripping + Leaf
    asBinds.
  * Q85 — nested ctor destructuring — subsumed by S(c, P).
  * Q86 — or-patterns — subsumed by row expansion pre-pass.

The conformance tests for each (tests 59–63 + a new 64 for
or-patterns) must all pass byte-identically after N11 integration.
The Q81–Q86 ad-hoc code is deleted in N11.


## 8. What Maranget does NOT cover (future work)

  * Record patterns (`User { name, age, .. } => …`) — deferred;
    when added, they specialize like ctors with a fixed ctor.
  * Literal patterns (`0 => a; 1 => b; _ => c`) — deferred;
    Maranget handles these via the "extended signature" refinement
    (§3.3 in the paper).  FX's Nat literals expand to Peano ctor
    patterns which Maranget handles natively.
  * GADT-style pattern refinement (pattern determines type arg) —
    requires coverage-checking extension beyond Maranget's basic
    algorithm.
  * Column-ordering heuristics (Maranget §4 "good decision trees")
    — FX uses leftmost-non-wildcard; optimal ordering is a
    performance concern, not a correctness concern.
