import FX.Syntax.Ast
import FX.Kernel.Term
import FX.Elab.NamedArgs

/-!
# N-series — Maranget pattern-matching kernel (N2 data types)

Per `docs/maranget.md` §2.  This file defines the three data types
Maranget compilation reads and writes:

  * `Row` — one row of the clause matrix.  Represents either a
    source `match` arm or one expansion of an or-pattern.  Carries
    the arm's original source index (`armIdx`) across or-pattern
    expansion so useless-clause diagnostics attribute back to the
    right source line.
  * `ClauseMatrix` — ordered `Array Row`.  Row order is the source
    arm order; Maranget's algorithm preserves it through
    specialization and default operations.
  * `DecisionTree` — the algorithm's output.  Three shapes:
      - `leaf` emits an arm body; may be guarded, in which case it
        carries a `fallthrough` sub-tree executed when the guard
        fails.
      - `switch` inspects column `col` of the scrutinee vector and
        dispatches per-ctor, with an optional fallback branch for
        ctors not explicitly covered.
      - `fail` signals an uncovered pattern space.  `witness`
        carries a specific pattern vector the algorithm proved is
        unreachable; diagnostics render it as the "missing case"
        example.

No algorithm lives in this file — N3 adds specialization, N4 adds
compile, N5–N7 layer in or/as/guards, N8–N9 add exhaustiveness
and useless-clause detection, N10 lowers trees to kernel terms,
N11 integrates into `elabMatch`, N12 validates via conformance.

Scope of N2:

  * Three data types above.
  * Pretty-printers suitable for `fxi dump --maranget` debugging
    (not yet wired into the CLI).
  * Smoke tests asserting constructors exist — builds against
    `lake build` so regressions land fast.
-/

namespace FX.Elab.Maranget

open FX.Syntax
open FX.Syntax.Ast

/-! ## Data types -/

/-- One row in a Maranget clause matrix.

    Fields:
      * `patterns` — the pattern vector, one entry per column.
        The matrix's columns correspond to a scrutinee vector; at
        top level `match` on a single expression has one column.
        Specialization `S(c, P)` (N3) expands ctor-args into new
        columns at position 0, so inner rows are wider than the
        initial vector.
      * `guard` — the arm's `if ...` guard.  If `some g`, the row's
        leaf emission wraps in `if g then body else fallthrough`.
      * `body` — the arm's body expression.
      * `armIdx` — the index of the source arm this row derives
        from.  Preserved across or-pattern expansion (N5) so one
        source arm producing `k` rows still reports as one arm in
        diagnostics.  Useless-clause detection (N9) reports an
        armIdx as dead iff ALL rows sharing that index are dead.
      * `asBinds` — pairs `(col, name)` collected from
        as-patterns stripped in pre-pass (N6).  At leaf lowering
        (N10), each binding projects column `col` of the scrutinee
        vector into the named let in the body's scope.
      * `span` — the source-level arm span, used for diagnostics.
-/
structure Row where
  patterns : Array Pattern
  guard    : Option Expr
  body     : Expr
  armIdx   : Nat
  asBinds  : Array (Nat × String)
  span     : Span
  deriving Inhabited

/-- A clause matrix is an ordered list of rows.  Order is the
    original source-arm order (first match wins semantics at
    runtime); `S` and `D` operations (N3) preserve relative
    order of surviving rows. -/
abbrev ClauseMatrix : Type := Array Row

/-- The output of Maranget compilation.

    Invariants (checked by N4's compile at construction time):
      * `Leaf.guard = some _ ↔ Leaf.fallthrough = some _`.
        An unguarded leaf always fires; `fallthrough` is
        meaningless and must be `none`.  A guarded leaf must
        have a fallthrough (which may itself be `fail` if the
        matrix had no rows to fall through to).
      * `Switch.branches` is ordered by ctor index (as declared
        in the spec), so kernel lowering can emit the methods
        list in the order `indRec` expects.
      * `Switch.fallbackBranch = none` iff `branches` covers the
        spec's full ctor set (a "complete signature" per
        Maranget §3).
-/
inductive DecisionTree where
  /-- Emit the arm body.  When `guard = some _`, runtime-evaluate
      the guard; on true, emit `body`; on false, dispatch to
      `fallthrough`.  When `guard = none`, `fallthrough` MUST be
      `none` (dead field). -/
  | leaf
      (body : Expr)
      (guard : Option Expr)
      (asBinds : Array (Nat × String))
      (fallthrough : Option DecisionTree)
      (span : Span)
      : DecisionTree
  /-- Inspect column `col` of the scrutinee vector; dispatch on
      its head constructor.  `specName` names the inductive spec
      (`"Nat"`, `"Option"`, user-enum `"color"`, …) the
      scrutinee's type resolves to — kernel lowering uses it to
      build the correct `Term.indRec` node.  `branches` carries
      one `(ctorIndex, subtree)` per ctor explicitly matched;
      `fallbackBranch` covers ctors not in `branches`. -/
  | switch
      (col : Nat)
      (specName : String)
      (branches : Array (Nat × DecisionTree))
      (fallbackBranch : Option DecisionTree)
      (span : Span)
      : DecisionTree
  /-- No arm covers this sub-space.  `witness` is a concrete
      pattern vector that reaches this `fail` leaf — rendered in
      E010 diagnostics as the missing-case example.  A `fail`
      reachable from the tree root means the match is
      non-exhaustive; a `fail` as the fallthrough of an
      unguarded leaf is dead code the lowering elides. -/
  | fail
      (witness : Array Pattern)
      (span : Span)
      : DecisionTree
  deriving Inhabited


/-! ## Matrix operations — Specialization S(c, P) and Default D(P)

Per `docs/maranget.md` §3.1–§3.2.  These are the two building blocks
from which N4's `compile` assembles a decision tree.  Each operation
produces a smaller matrix: `S` restricts to the world where column 0
matches constructor `c`, and `D` restricts to the world where column
0 is a catch-all pattern (the "default" branch of a switch node).

Both operations preserve the relative order of surviving rows — this
is what makes Maranget's algorithm respect first-match semantics end
to end. -/

/-- Strip `ascribed` pattern wrappers to expose the inner pattern.
    Type ascriptions (`pat : T`) don't affect pattern matching — they
    resolve at typing time, not at match time, so the matrix
    operations see through them. -/
partial def stripAscription : Pattern → Pattern
  | .ascribed inner _ _ => stripAscription inner
  | other               => other

/-- Is a pattern a wildcard or variable?  Both behave identically
    under specialization and default: they match any scrutinee.  The
    `var` name was lifted into the row's `asBinds` by N6's pre-pass
    (N6 not yet landed — this is a forward invariant); at the matrix-
    operation layer we don't distinguish the two. -/
def isCatchAll (pat : Pattern) : Bool :=
  match stripAscription pat with
  | .wildcard _ => true
  | .var _ _    => true
  | _           => false

/-- Outcome of classifying a row's head pattern against a target ctor.

      * `matchesCtor args` — column 0 is the target ctor; row
        survives specialization, with its `args` inlined as the new
        columns 0..k-1.
      * `matchesAny` — column 0 is wildcard/var; row survives with
        `k` wildcards inlined as the new columns 0..k-1.
      * `matchesNothing` — column 0 is a different ctor; row is
        dropped from the specialized matrix.
      * `invariantViolation` — column 0 is a literal, tuple, or
        un-stripped as/or-pattern.  Those cases should have been
        handled by the N5/N6 pre-passes (and literals/tuples are
        future work per `docs/maranget.md` §8); callers defensively
        drop such rows, but the elaborator should have rejected them
        before reaching the matrix operations. -/
inductive HeadOutcome where
  | matchesCtor        (args : Array Pattern)
  | matchesAny
  | matchesNothing
  | invariantViolation

/-- Classify a row's column-0 pattern relative to a target ctor name.
    Only the ctor's `final` segment is compared — qualifier resolution
    happened during elaboration; by the time Maranget sees patterns
    they reference the canonical ctor name of the matched IndSpec. -/
def classifyHead (ctorName : String) (pat : Pattern) : HeadOutcome :=
  match stripAscription pat with
  | .wildcard _       => .matchesAny
  | .var _ _          => .matchesAny
  | .ctor qual args _ =>
    if qual.final == ctorName then .matchesCtor args
    else .matchesNothing
  | .literal _ _      => .invariantViolation
  | .tuple _ _        => .invariantViolation
  | .asPattern _ _ _  => .invariantViolation
  | .orPattern _ _    => .invariantViolation  -- N5 expand pre-pass
  | .ascribed _ _ _   => .invariantViolation  -- stripAscription handled

/-- Build a vector of `arity` wildcard patterns.  Used when
    specializing a row whose column 0 is a wildcard/var: the wildcard
    stands in for every possible ctor, so when we're down-selecting to
    the world where col 0 matched the target ctor, we replace that
    single catch-all with `arity` catch-alls — one per ctor arg.  Uses
    `Span.zero` because synthesized wildcards have no source origin;
    callers using a row's span pass it explicitly. -/
def wildcardVector (arity : Nat) : Array Pattern :=
  Array.replicate arity (Pattern.wildcard Span.zero)

/-- Specialize one row on ctor `ctorName` of arity `arity`.  Returns
    `some row'` if the row survives, `none` if it's dropped.  See
    `docs/maranget.md` §3.1 for the full specification.

    Arity mismatch (column 0 is a ctor-pattern with the right name
    but wrong argument count) is treated as a drop — this is a
    spec-level inconsistency the elaborator should have rejected
    before reaching Maranget.  We defensively drop rather than panic
    so a single malformed row doesn't sink the whole compilation. -/
def specializeRow (ctorName : String) (arity : Nat)
    (row : Row) : Option Row :=
  if row.patterns.isEmpty then
    none
  else
    let col0 := row.patterns[0]!
    let rest := row.patterns.extract 1 row.patterns.size
    match classifyHead ctorName col0 with
    | .matchesAny =>
      some { row with patterns := wildcardVector arity ++ rest }
    | .matchesCtor args =>
      if args.size == arity then
        some { row with patterns := args ++ rest }
      else
        none  -- arity mismatch; spec-level inconsistency
    | .matchesNothing => none
    | .invariantViolation => none

/-- `S(c, P)` — specialize matrix `P` on constructor `ctorName` with
    arity `arity`.  Produces a new matrix with:

      * Rows where column 0 is `ctorName(args)` survive, with `args`
        replacing column 0 (so the matrix grows `arity - 1` columns).
      * Rows where column 0 is a catch-all survive, with `arity`
        wildcards replacing column 0.
      * Rows where column 0 is a different ctor are dropped.

    Row order among survivors is preserved — first-match semantics
    carry through to the sub-matrix.

    `asBinds` propagate unchanged.  Their column indices index the
    pattern vector at the moment of as-stripping (N6 pre-pass); the
    N10 lowering uses the decision tree structure to reconstruct the
    scrutinee path, so no index remapping is needed here. -/
def specialize (ctorName : String) (arity : Nat)
    (matrix : ClauseMatrix) : ClauseMatrix :=
  matrix.filterMap (specializeRow ctorName arity)

/-- Default-op per row: survive if column 0 is catch-all (with col 0
    dropped), else drop.  A helper for `defaultMatrix`. -/
def defaultRow (row : Row) : Option Row :=
  if row.patterns.isEmpty then
    none
  else
    let col0 := row.patterns[0]!
    if isCatchAll col0 then
      some { row with patterns := row.patterns.extract 1 row.patterns.size }
    else
      none

/-- `D(P)` — default matrix.  Produces a new matrix containing only
    rows whose column 0 is a catch-all (wildcard or variable), with
    column 0 dropped.  Used by Compile (N4) to build the `fallback`
    branch of a Switch node, covering the case where the scrutinee's
    head ctor isn't matched by any of the explicit branches.

    Row order among survivors preserved; `asBinds` propagate
    unchanged for the same reason as in `specialize`. -/
def defaultMatrix (matrix : ClauseMatrix) : ClauseMatrix :=
  matrix.filterMap defaultRow


/-! ## N5 — Or-pattern row expansion

Per `docs/maranget.md` §3.4.  A row containing an or-pattern
`p_1 | p_2 | ... | p_k` at any position expands into `k` rows, each
with one alternative substituted at that position.  All expanded
rows share the same `armIdx`, `guard`, `body`, `span`, and
`asBinds` — so useless-clause detection (N9) can still attribute a
dead arm back to the single source location.

This pre-pass is what structurally prevents the Q85+Q86 silent-
drop bug.  The legacy `findSome?`-based ctor-arm matching only
ever found the FIRST arm for a given ctor — an or-pattern with
multiple alternatives covering the same outer ctor (e.g.,
`Zero | Succ(Zero) | Succ(Succ(Zero))`) silently dropped all but
the first `Succ(...)` alternative.  After N5 expansion, each
alternative becomes its own row; `specialize` / `defaultMatrix`
see them individually and N9 catches any genuinely dead row.

Expansion is DEEP: nested or-patterns inside ctor args / tuple
items / as-patterns / ascriptions are also distributed.  `Succ(A | B)`
expands to `[Succ(A), Succ(B)]`; `Succ(A | B) as n` expands to
`[Succ(A) as n, Succ(B) as n]`.  Worst-case exponential in or-
pattern count but in practice shallow. -/

/-- All alternative patterns of a pattern after deep or-pattern
    distribution.  For a bare `orPattern [p1, p2, ...]` returns
    the concatenation of each alternative's expansion.  For ctor
    / tuple / ascribed / asPattern wrappers, returns the cartesian
    product of children's expansions wrapped in the same
    constructor.  For wildcard / var / literal returns `[self]`. -/
partial def expandPattern : Pattern → Array Pattern
  | .orPattern alts _ =>
    alts.foldl (init := #[]) fun acc alt =>
      acc ++ expandPattern alt
  | .ctor qual args span =>
    let argCombos : Array (Array Pattern) :=
      args.foldl (init := #[#[]]) fun partialCombos arg =>
        let argAlts := expandPattern arg
        partialCombos.foldl (init := #[]) fun combined priorArgs =>
          argAlts.foldl (init := combined) fun combined' altArg =>
            combined'.push (priorArgs.push altArg)
    argCombos.map fun combo => .ctor qual combo span
  | .tuple items span =>
    let itemCombos : Array (Array Pattern) :=
      items.foldl (init := #[#[]]) fun partialCombos item =>
        let itemAlts := expandPattern item
        partialCombos.foldl (init := #[]) fun combined priorItems =>
          itemAlts.foldl (init := combined) fun combined' altItem =>
            combined'.push (priorItems.push altItem)
    itemCombos.map fun combo => .tuple combo span
  | .ascribed inner typeExpr span =>
    (expandPattern inner).map fun alt => .ascribed alt typeExpr span
  | .asPattern inner name span =>
    (expandPattern inner).map fun alt => .asPattern alt name span
  | .wildcard span => #[.wildcard span]
  | .var name span => #[.var name span]
  | .literal tok span => #[.literal tok span]

/-- Expand one row: returns all rows produced by distributing or-
    patterns across the pattern vector.  Each resulting row shares
    the original's `armIdx`, `guard`, `body`, `span`, `asBinds`
    — only `patterns` changes.

    Cartesian product: for a row with columns [p, q] where p has
    alternatives [a, b] and q has alternatives [c, d], produces
    rows with patterns [a,c], [a,d], [b,c], [b,d]. -/
def expandRow (row : Row) : Array Row :=
  let patternCombos : Array (Array Pattern) :=
    row.patterns.foldl (init := #[#[]]) fun partialCombos pat =>
      let alts := expandPattern pat
      partialCombos.foldl (init := #[]) fun combined priorCols =>
        alts.foldl (init := combined) fun combined' altCol =>
          combined'.push (priorCols.push altCol)
  patternCombos.map fun combo => { row with patterns := combo }

/-- `expandOrPatterns` — the N5 pre-pass on a full matrix.  Every
    row is expanded via `expandRow`; the results are concatenated
    in original row order.  After this pass, no `orPattern` node
    remains anywhere in any row's pattern tree — subsequent matrix
    operations (S, D, compile) can assume or-pattern-free input. -/
def expandOrPatterns (matrix : ClauseMatrix) : ClauseMatrix :=
  matrix.foldl (init := #[]) fun acc row =>
    acc ++ expandRow row


/-! ## N6 — As-pattern stripping (named binding layer)

Per `docs/maranget.md` §3.5.  `pat as name` at any column of a row
is stripped to `pat`, and the binding `(column, name)` is recorded
in the row's `asBinds`.  At leaf emission (N10) each binding
materializes as a `let name = scrutinee_at_col` wrapping the
body — the same β-redex mechanism Q82/Q84 used, applied uniformly
to every row that accumulated binds.

Scope of N6: TOP-LEVEL as-patterns at the row's pattern-vector
columns.  `Zero as z`, `Succ(n) as total`, `((Zero as m) as n)` —
all handled: double-wrapped as peels recursively, producing
multiple binds with the same column.

What N6 does NOT cover: as-patterns deeper than row-top-level,
such as `Cons(h, t as rest)` — the `rest` binding refers to a
sub-component of col 0, not col 0 itself, and representing that
requires a path-based binding model (Array Nat, not single Nat).
The helper `hasDeeplyNestedAsPattern` detects these; N11
integration should reject such rows with a clear E010 until the
path-based machinery lands.  For FX's current surface-syntax
coverage (Q84's top-of-arm as-bindings), top-level is sufficient. -/

/-- Peel outer `asPattern` wrappers at column `col`, recording each
    binding as `(col, name)`.  For `((p as m) as n)` produces
    `(p, [(col, m), (col, n)])` — inner binding first, outer
    binding last.  At leaf emission (N10) this order matters only
    for shadowing semantics: if the user writes two `as` with the
    same name on the same value, the outermost wins (it's in scope
    at the body).  Non-as patterns return unchanged with an empty
    bind list. -/
partial def stripAsAtCol (col : Nat) : Pattern → Pattern × Array (Nat × String)
  | .asPattern inner name _ =>
    let (innerStripped, innerBinds) := stripAsAtCol col inner
    (innerStripped, innerBinds.push (col, name))
  | other => (other, #[])

/-- Strip top-level as-patterns from each pattern-vector column of
    a single row.  Collected binds append to the row's existing
    `asBinds`.  Does NOT descend into ctor args / tuple items /
    ascriptions — those are the caller's responsibility to reject
    (see `hasDeeplyNestedAsPattern`) until path-based binding
    lands. -/
def stripAsFromRow (row : Row) : Row := Id.run do
  let mut strippedPatterns : Array Pattern := Array.mkEmpty row.patterns.size
  let mut accumulatedBinds : Array (Nat × String) := row.asBinds
  for col in [:row.patterns.size] do
    let (strippedPat, colBinds) := stripAsAtCol col row.patterns[col]!
    strippedPatterns := strippedPatterns.push strippedPat
    accumulatedBinds := accumulatedBinds ++ colBinds
  return { row with patterns := strippedPatterns, asBinds := accumulatedBinds }

/-- N6 pre-pass: strip top-level as-patterns from every row of the
    matrix.  Row count unchanged; within each row, top-level as
    wrappers at each column become entries in `asBinds`.  Order
    among rows preserved. -/
def stripAsFromMatrix (matrix : ClauseMatrix) : ClauseMatrix :=
  matrix.map stripAsFromRow

/-- Does this pattern contain ANY `asPattern` node, at any depth? -/
partial def patternHasAnyAsPattern : Pattern → Bool
  | .asPattern _ _ _     => true
  | .ctor _ args _       => args.any patternHasAnyAsPattern
  | .tuple items _       => items.any patternHasAnyAsPattern
  | .ascribed inner _ _  => patternHasAnyAsPattern inner
  | .orPattern alts _    => alts.any patternHasAnyAsPattern
  | .wildcard _          => false
  | .var _ _             => false
  | .literal _ _         => false

/-- Does this pattern contain an as-pattern DEEPER than its
    immediate top level?  Used by the N11 integration to flag
    patterns N6 can't handle soundly — nested binds need a path-
    based representation, so we reject rather than silently drop.

    Top-level single as (`Zero as z`) is fine — the outer wrapper
    is peeled by `stripAsAtCol`, and its inner has no further as.
    Top-level chained as (`(p as m) as n`) is also fine — the peel
    recurses through the chain.  But as inside ctor args / tuple
    items / ascription / orPattern alternatives is nested and
    triggers this check. -/
partial def hasDeeplyNestedAsPattern : Pattern → Bool
  | .asPattern inner _ _ =>
    -- Top-level as peels cleanly.  Check inner: if it itself has
    -- ANY as-pattern at ANY depth in ctor args / tuple items /
    -- ascription / orPattern, that's nested from the row col's
    -- perspective.  A bare chained as (`(p as m) as n`) is fine
    -- because peeling the outer exposes a top-level `p as m`.
    hasDeeplyNestedAsPattern inner
  | .ctor _ args _       => args.any patternHasAnyAsPattern
  | .tuple items _       => items.any patternHasAnyAsPattern
  | .ascribed inner _ _  => patternHasAnyAsPattern inner
  | .orPattern alts _    => alts.any patternHasAnyAsPattern
  | .wildcard _          => false
  | .var _ _             => false
  | .literal _ _         => false


/-! ## N4 — Core compile: ClauseMatrix → DecisionTree

The heart of Maranget's algorithm.  `compile` turns a matrix into a
decision tree via ctor dispatch.  It uses a callback (`CompileCtx`)
to look up inductive-spec metadata — arity, argument specs, and the
full ctor set for complete-signature detection.  N11 plumbs that
callback in from the elaborator's `IndSpec` registry; N4 stays
kernel-free so the algorithm is testable in isolation.

Scope of N4: ctor dispatch + Leaf emission + Fail for uncovered
branches.  Or-patterns (N5), as-patterns (N6), and guard-specific
refinements (N7) compose by pre-passes that run before `compile`;
exhaustiveness reporting (N8) and useless-clause detection (N9) run
after `compile` and consume its DecisionTree output. -/

/-- Descriptor of one constructor of an inductive spec, supplied to
    `compile` via `CompileCtx.lookupSpec`.

      * `name` — the ctor's final-segment name (unqualified; ctor
        resolution happened during elaboration before Maranget ran).
      * `arity` — number of arguments the ctor takes.
      * `argSpecs` — spec name of each argument, used when recursing
        into sub-matrices after `specialize`.  For non-inductive arg
        types (e.g., `i64`, record types), callers pass a sentinel
        name the matrix will only reach via catch-all rows — no
        further ctor dispatch happens on those columns so the
        sentinel is never looked up.
      * `ctorIndex` — index in the spec's ctor list, matching the
        order `indRec` expects at lowering.  `Switch.branches` is
        sorted by this index. -/
structure CtorInfo where
  name      : String
  arity     : Nat
  argSpecs  : Array String
  ctorIndex : Nat
  deriving Inhabited

/-- Context for Maranget compilation — resolves spec names to their
    ctor lists.  Supplied by the caller at integration (N11).  The
    callback returns `none` for unknown specs; well-formed elab
    never passes an unknown name (every scrutinee's type was
    resolved before Maranget ran), so `compile` treats `none` as an
    invariant violation and emits `Fail` defensively. -/
structure CompileCtx where
  lookupSpec : String → Option (Array CtorInfo)

/-- Enumerate distinct ctors appearing in column 0 of the matrix, in
    first-appearance order across rows.  Catch-alls (wildcards,
    vars, ascribed catch-alls) don't contribute ctors.  Other non-
    ctor shapes (literal, tuple, un-stripped as/or patterns) are
    also skipped — they're pre-pass invariants Maranget assumes
    handled. -/
def ctorsAtCol0 (matrix : ClauseMatrix) : Array String :=
  matrix.foldl (init := #[]) fun seen row =>
    if row.patterns.isEmpty then seen
    else
      match stripAscription row.patterns[0]! with
      | .ctor qual _ _ =>
        if seen.contains qual.final then seen
        else seen.push qual.final
      | _ => seen

/-- Is every pattern in this row a catch-all (wildcard or variable,
    with ascriptions stripped)?  Used by `compile` to detect Leaf
    base cases. -/
def isAllCatchAll (row : Row) : Bool :=
  row.patterns.all isCatchAll

/-- A pattern vector of `n` wildcards with the given span, used as
    the witness for `Fail` nodes in `compile`'s base cases.  N8
    will refine witnesses to specific missing-pattern examples; N4
    just uses all-wildcards as a placeholder. -/
def wildcardWitness (width : Nat) (span : Span) : Array Pattern :=
  Array.replicate width (Pattern.wildcard span)

/-- Replace col 0 of a spec-name vector with the arg-spec vector for
    a ctor of arity k.  Used when recursing into `S(c, P)`.
    Precondition: `specs.size ≥ 1`. -/
def specsAfterSpecialize (specs : Array String)
    (argSpecs : Array String) : Array String :=
  argSpecs ++ specs.extract 1 specs.size

/-- Drop col 0 from a spec-name vector.  Used when recursing into
    `D(P)`.  Precondition: `specs.size ≥ 1`. -/
def specsAfterDefault (specs : Array String) : Array String :=
  specs.extract 1 specs.size

/-- Core compile recursion.  Per `docs/maranget.md` §3.3.

    Invariants maintained:

      * `colSpecs.size = width(matrix)` — one spec name per column.
        All rows of `matrix` have `patterns.size = colSpecs.size`.
      * Or-patterns and as-patterns have been stripped by pre-passes
        (N5 and N6, not yet landed).  `compile` defensively treats
        un-stripped pattern shapes as non-matching rows via
        `classifyHead`'s `invariantViolation` branch.

    Termination: each recursive call produces either a strictly
    smaller matrix (fewer rows via `defaultMatrix` or `specialize`
    with dropping) or a structurally simpler matrix (one column
    compressed into ctor args — `specialize` with ctor-match).  A
    total termination proof is future work under the R-series.

    The three cases mirror §3.3 steps 1/2 and 3/4/5:

      1. Empty matrix — `Fail` with width-many wildcards.
      2. Head row all catch-alls — `Leaf` from the head row.
         Fallthrough is `Compile(tail)` if the head has a guard,
         else `none` (unguarded leaf always fires; tail is dead).
      3. At least one ctor in col 0 — enumerate ctors, recurse per
         ctor via `specialize`, recurse on `defaultMatrix` if the
         ctor set is incomplete, emit `Switch`.

    Guard handling (N7, per `docs/maranget.md` §3.6): guards live
    ONLY on `Leaf` nodes by construction — `Switch` has no guard
    field.  The composition works uniformly because:

      * A row with a guard and ctor-specific col-0 pattern hits
        case 3, specializes into a sub-matrix.  `specializeRow`
        preserves `row.guard` via `{ row with patterns := ... }`,
        so the guard travels into the branch where it applies.

      * When the row eventually becomes all-catch-alls in some
        sub-matrix (after enough specialize steps), case 2 fires
        and emits `Leaf body (some guard) asBinds (some tailTree)`
        where `tailTree = compile(matrix.tail)`.

      * An unguarded catch-all head emits `Leaf body none asBinds
        none` — tail is unreachable code, correctly elided.

      * A guarded catch-all head with empty tail produces `Leaf
        body (some guard) asBinds (some (Fail ...))` — if the
        guard fails at runtime, execution hits Fail, signalling
        non-exhaustive coverage.  N8/N9 detect this statically. -/
partial def compile
    (ctx : CompileCtx)
    (colSpecs : Array String)
    (matrix : ClauseMatrix)
    : DecisionTree :=
  if matrix.isEmpty then
    DecisionTree.fail (wildcardWitness colSpecs.size Span.zero) Span.zero
  else
    let headRow := matrix[0]!
    if isAllCatchAll headRow then
      let fallthrough : Option DecisionTree :=
        match headRow.guard with
        | none   => none
        | some _ =>
          let tail := matrix.extract 1 matrix.size
          some (compile ctx colSpecs tail)
      DecisionTree.leaf headRow.body headRow.guard headRow.asBinds
        fallthrough headRow.span
    else if colSpecs.isEmpty then
      -- Width-0 matrix with a non-catch-all row is an invariant
      -- violation (no column to dispatch on).  Emit Fail.
      DecisionTree.fail #[] headRow.span
    else
      let col0Spec := colSpecs[0]!
      let ctorsInMatrix := ctorsAtCol0 matrix
      match ctx.lookupSpec col0Spec with
      | none =>
        DecisionTree.fail (wildcardWitness colSpecs.size Span.zero)
          headRow.span
      | some specCtors =>
        let branches :=
          ctorsInMatrix.foldl (init := #[]) fun acc ctorName =>
            match specCtors.find? (fun info => info.name == ctorName) with
            | none      => acc  -- ctor not in spec; elab would
                                -- have rejected — skip defensively
            | some info =>
              let subMatrix := specialize ctorName info.arity matrix
              let subSpecs  := specsAfterSpecialize colSpecs info.argSpecs
              let subtree   := compile ctx subSpecs subMatrix
              acc.push (info.ctorIndex, subtree)
        let branchesSorted :=
          branches.qsort (fun left right => left.1 < right.1)
        let isComplete :=
          specCtors.all fun info => ctorsInMatrix.contains info.name
        let fallback : Option DecisionTree :=
          if isComplete then none
          else
            let subMatrix := defaultMatrix matrix
            let subSpecs  := specsAfterDefault colSpecs
            some (compile ctx subSpecs subMatrix)
        DecisionTree.switch 0 col0Spec branchesSorted fallback headRow.span


/-! ## N8 — Exhaustiveness predicate `useful(P, q)`

Per `docs/maranget.md` §3.7 (Maranget 2008 §3.1).  `useful(P, q)`
decides: "is there a value that the pattern vector `q` matches but
no row of `P` matches?"  Two headline uses:

  * **Exhaustiveness**: `useful(fullMatrix, wildcardVector)` — a
    match is non-exhaustive iff this returns `true`.  The wildcard
    vector represents "any value at any column"; if some such
    value is not covered by the arms, exhaustiveness fails.
    (N11 will emit E010 at this point.)

  * **Useless clause** (N9): for each arm `i`, check
    `useful(rows[0..i-1], rows[i].patterns)` — if `false`, arm
    `i` is unreachable.  N9 implements that wrapper.

The algorithm mirrors `compile`'s structure.  Three cases:

  1. `colSpecs.size = 0` — the matching happens at the empty
     scrutinee vector.  `useful` is `true` iff the matrix has no
     rows (a row with empty patterns matches the empty vector
     vacuously, so any row blocks).

  2. `q[0]` is a ctor `c(args)` — specialize on `c` and recurse:
     `useful(S(c, P), (args, q[1..]))`.

  3. `q[0]` is a catch-all (wildcard or var) — split on whether
     the matrix's col-0 ctor set `Σ` covers the full spec:

       * Complete signature: `∨_{c ∈ spec} useful(S(c, P),
         (wildcards_c, q[1..]))` — useful iff some ctor's
         specialization leaves q useful.
       * Incomplete signature: `useful(D(P), q[1..])` — the
         default branch's sub-problem.

Defensive conservatism: unknown spec names, arity mismatches,
literal/tuple heads in `q`, un-stripped as- or or-patterns — all
return `true`.  Overapproximating the "useful" answer means we
might FAIL to flag a reachable bug but never incorrectly flag a
valid match as bad, which fits E010's role as a hard error:
false-positives would block legitimate code.

Termination: each recursive call either reduces `matrix.size` (via
specialize dropping rows for a ctor mismatch) or reduces
`colSpecs.size` (via specsAfterDefault or the width-0 base case).
Marked `partial` pending a formal termination proof (R-series). -/
partial def useful
    (ctx : CompileCtx)
    (colSpecs : Array String)
    (matrix : ClauseMatrix)
    (q : Array Pattern)
    : Bool :=
  if colSpecs.isEmpty then
    matrix.isEmpty
  else if q.isEmpty then
    true  -- invariant violation (q.size != colSpecs.size); conservative
  else
    let q0         := stripAscription q[0]!
    let qRest      := q.extract 1 q.size
    let col0Spec   := colSpecs[0]!
    match q0 with
    | .ctor qual args _ =>
      match ctx.lookupSpec col0Spec with
      | none => true  -- unknown spec; conservative
      | some specCtors =>
        match specCtors.find? (fun info => info.name == qual.final) with
        | none => true  -- ctor not in spec; conservative
        | some info =>
          if args.size != info.arity then
            true  -- arity mismatch; conservative
          else
            let subMatrix := specialize qual.final info.arity matrix
            let subSpecs  := specsAfterSpecialize colSpecs info.argSpecs
            useful ctx subSpecs subMatrix (args ++ qRest)
    | _ =>
      if isCatchAll q0 then
        match ctx.lookupSpec col0Spec with
        | none => true  -- unknown spec; conservative
        | some specCtors =>
          let ctorsInP := ctorsAtCol0 matrix
          let isComplete := specCtors.all
            fun info => ctorsInP.contains info.name
          if isComplete then
            specCtors.any fun info =>
              let subMatrix := specialize info.name info.arity matrix
              let subSpecs  := specsAfterSpecialize colSpecs info.argSpecs
              let subQ      := wildcardVector info.arity ++ qRest
              useful ctx subSpecs subMatrix subQ
          else
            let subMatrix := defaultMatrix matrix
            let subSpecs  := specsAfterDefault colSpecs
            useful ctx subSpecs subMatrix qRest
      else
        -- Literal, tuple, un-stripped as- or or-pattern — N5/N6
        -- pre-passes should have normalized these out; conservative.
        true

/-- Exhaustiveness wrapper: `isExhaustive` returns `true` iff the
    matrix covers every value of the scrutinee vector's type.
    Equivalent to `not (useful matrix wildcards)` where `wildcards`
    is the all-wildcard vector of appropriate width. -/
def isExhaustive
    (ctx : CompileCtx)
    (colSpecs : Array String)
    (matrix : ClauseMatrix)
    : Bool :=
  let wildcards := wildcardVector colSpecs.size
  not (useful ctx colSpecs matrix wildcards)


/-! ## N9 — Useless-clause detection

Per `docs/maranget.md` §3.7.  `uselessArms` builds on N8's
`useful` predicate to detect arms whose patterns are subsumed by
earlier arms — they can never fire at runtime.  N11 emits W001
per returned armIdx; release mode treats W001 as an error per
§10.12.

Per-ARM (not per-row) semantics: N5's or-pattern expansion
produces multiple rows with the same `armIdx` from one source
arm.  An arm is useless iff ALL its rows are useless; a single
useful row keeps the arm alive.  This is why we return `armIdx`
values, not row indices — diagnostics should point at source
arms, not synthesized expansion rows.

The check per row: `useful(matrix[0..i-1], matrix[i].patterns)`
over the PREFIX of prior rows.  Same-arm siblings (from or-
expansion) appear in the prefix — but since any useful sibling
is enough to keep the arm alive, per-arm aggregation washes that
out.  Formally: arm `a` is dead iff for every row with armIdx
`a`, that row is subsumed by prior rows (including siblings).

Conservative `useful` returning `true` on invariant violations
(unknown spec, arity mismatch, un-stripped as/or) keeps arms
alive in the face of pre-pass bugs — a false-positive-dead arm
would silently delete user code, which is the worst kind of
wrong.  Conservative-alive is safe. -/
def uselessArms
    (ctx : CompileCtx)
    (colSpecs : Array String)
    (matrix : ClauseMatrix)
    : Array Nat := Id.run do
  -- Step 1: find arms with at least one useful row.  A row is
  -- useful iff its pattern vector is useful against the prefix
  -- of prior rows.
  let mut armsWithUsefulRow : Array Nat := #[]
  for i in [:matrix.size] do
    let priorRows := matrix.extract 0 i
    let row := matrix[i]!
    if useful ctx colSpecs priorRows row.patterns then
      if !armsWithUsefulRow.contains row.armIdx then
        armsWithUsefulRow := armsWithUsefulRow.push row.armIdx
  -- Step 2: collect all armIdx values in original order of first
  -- appearance.  This is the universe of arms we'll classify.
  let mut allArms : Array Nat := #[]
  for row in matrix do
    if !allArms.contains row.armIdx then
      allArms := allArms.push row.armIdx
  -- Step 3: dead arms = allArms \ armsWithUsefulRow, preserving
  -- first-appearance order so diagnostics emit in source-file
  -- order.
  return allArms.filter (fun armIdx => !armsWithUsefulRow.contains armIdx)


/-! ## N10 — Lower DecisionTree → kernel Term

Per `docs/maranget.md` §4.  The lowering walks a DecisionTree and
emits a kernel `Term` (ultimately built from `Term.indRec` for
Switch nodes, straight body terms for unguarded Leaves, and
`Term.indRec` on Bool for guards).

**Design**: N10 owns the TREE WALK — visit each node in the
right order, thread errors through, compose sub-results.  The
actual kernel-term-building is delegated to callbacks on a
`LowerCtx` that N11 provides.  This split is load-bearing:

  * Leaf body elaboration needs full elaborator state
    (globalEnv, scope, expected type).  That state lives in N11's
    elabMatch, not here.  The `emitLeaf` callback wraps it.

  * Switch emission needs per-spec motive construction, method
    lambda chains over ctor args, grade annotations, de-Bruijn
    shifting.  Already implemented in the legacy elabMatch for
    Q81-Q85; N11 reuses that via `emitSwitch`.

  * Guard emission needs Bool's indRec + an if-then-else shape.
    N11 wires this via `emitGuard`.

  * Fail emission at a REACHABLE site is an E010 error; at an
    unreachable site (fallthrough of an unguarded Leaf) it's
    dead code the walk never reaches.  `emitFail` decides the
    E010 message / witness rendering.

The invariant `Leaf.guard = some _ ↔ Leaf.fallthrough = some _`
(enforced by N4 `compile` construction) is checked here: a
malformed guarded Leaf (guard = some, fallthrough = none) would
be a bug in compile, so we return an internal-error on that
shape.  A well-formed tree never triggers it. -/

/-- Callbacks a caller (N11) provides to drive kernel-term
    emission during decision-tree lowering.  Each callback is
    `Except ElabError Term` so errors from body elaboration,
    motive construction, or non-exhaustive diagnostics bubble up
    uniformly. -/
structure LowerCtx where
  /-- Emit the Term for a Leaf node: elaborate `body` under the
      current scope extended with the `asBinds` let-bindings.
      The span is the leaf's span (for diagnostic anchoring). -/
  emitLeaf : Expr → Array (Nat × String) → Span →
             Except ElabError FX.Kernel.Term
  /-- Emit the Term for a Switch node.  `specName` is the
      inductive spec the switch dispatches on (passed to
      `Term.indRec`); `branches` is the ordered
      (ctorIndex, already-lowered-subtree) list; `fallback` is
      the optional default-branch lowered subtree.  The callback
      handles ctor arg binders, recursive-result binders, motive
      construction, and grade annotations. -/
  emitSwitch : (specName : String) → (branches : Array (Nat × FX.Kernel.Term))
               → (fallback : Option FX.Kernel.Term) → Span →
               Except ElabError FX.Kernel.Term
  /-- Emit the Term for a guarded Leaf: `if guard then body else
      fallthrough`.  N11 lowers this to `Term.indRec "Bool"`. -/
  emitGuard : (guard : Expr) → (body : FX.Kernel.Term) →
              (fallthrough : FX.Kernel.Term) → Span →
              Except ElabError FX.Kernel.Term
  /-- Emit the Term for a Fail node at a reachable position.
      Typically returns `Except.error` with an E010 non-
      exhaustive diagnostic mentioning the witness pattern. -/
  emitFail : (witness : Array Pattern) → Span →
             Except ElabError FX.Kernel.Term

/-- Lower a DecisionTree to a kernel Term via the callbacks on
    `LowerCtx`.  Pure tree walk: recurses structurally, composes
    sub-results, threads `Except ElabError` for diagnostic
    propagation.

    Termination: structural recursion on the DecisionTree.
    Marked `partial` because Lean can't prove it through the
    nested `Array.mapM` — a total version would unfold the
    Array recursion manually.  Future R-series work. -/
partial def lowerDecisionTree
    (ctx : LowerCtx) : DecisionTree → Except ElabError FX.Kernel.Term
  | .fail witness span =>
    ctx.emitFail witness span
  | .leaf body none asBinds _ span =>
    -- Unguarded Leaf: fallthrough is meaningless (invariant from
    -- N4), ignore it.  Just elaborate the body.
    ctx.emitLeaf body asBinds span
  | .leaf body (some guardExpr) asBinds (some fallthroughTree) span => do
    -- Guarded Leaf with fallthrough: elaborate body, lower
    -- fallthrough, combine via `emitGuard` into
    -- `if guard then body else fallthrough`.
    let bodyTerm ← ctx.emitLeaf body asBinds span
    let fallthroughTerm ← lowerDecisionTree ctx fallthroughTree
    ctx.emitGuard guardExpr bodyTerm fallthroughTerm span
  | .leaf _ (some _) _ none span =>
    -- Invariant violation: guarded Leaf must have fallthrough.
    -- N4 enforces this; if we see it, `compile` emitted a
    -- malformed tree.
    Except.error (ElabError.make "E010"
      "internal: guarded match arm emitted without fallthrough — compile produced a malformed DecisionTree (invariant: Leaf.guard = some ↔ Leaf.fallthrough = some)"
      span)
  | .switch _col specName branches fallback span => do
    -- Switch: lower each branch's subtree, optionally lower the
    -- fallback, delegate to `emitSwitch` for indRec construction.
    let loweredBranches ← branches.mapM fun (ctorIdx, subtree) => do
      let subtreeTerm ← lowerDecisionTree ctx subtree
      pure (ctorIdx, subtreeTerm)
    let loweredFallback : Option FX.Kernel.Term ← match fallback with
      | none   => pure none
      | some f => do
        let fTerm ← lowerDecisionTree ctx f
        pure (some fTerm)
    ctx.emitSwitch specName loweredBranches loweredFallback span


/-! ## Pretty-printers (for `fxi dump --maranget`, N-series
    debugging) -/

/-- Best-effort short-form pretty of an `Ast.Pattern`.  Not a
    round-trip serializer — just readable enough to identify the
    pattern in dump output.  Keeps the implementation small
    because full pattern printing lives in the parser/diagnostic
    path; here we only need enough fidelity for debugging. -/
partial def prettyPattern : Pattern → String
  | .wildcard _           => "_"
  | .var name _           => name
  | .literal _ _          => "<literal>"
  | .tuple items _        =>
    let itemStrs := items.toList.map prettyPattern
    s!"({String.intercalate ", " itemStrs})"
  | .ascribed inner _ _   => prettyPattern inner
  | .asPattern inner n _  => s!"{prettyPattern inner} as {n}"
  | .ctor q args _        =>
    let argStrs := args.toList.map prettyPattern
    let argsPart :=
      if args.isEmpty then ""
      else "(" ++ String.intercalate ", " argStrs ++ ")"
    q.final ++ argsPart
  | .orPattern alts _     =>
    String.intercalate " | " (alts.toList.map prettyPattern)

/-- Pretty-print one row of the clause matrix.  Format:
      `arm#{armIdx}: [pat0, pat1, ...] if <guard> [as binds]`
    The guard body and arm body are not rendered in full — the
    dump is for structural debugging, not source reconstruction. -/
def Row.pretty (row : Row) : String :=
  let pats := String.intercalate ", "
    (row.patterns.toList.map prettyPattern)
  let guardPart :=
    match row.guard with
    | some _ => " if <guard>"
    | none   => ""
  let bindsPart :=
    if row.asBinds.isEmpty then ""
    else
      let pairs := row.asBinds.toList.map
        (fun (col, name) => s!"col{col}={name}")
      " [" ++ String.intercalate ", " pairs ++ "]"
  s!"arm#{row.armIdx}: [{pats}]{guardPart}{bindsPart}"

/-- Pretty-print an entire clause matrix, one row per line. -/
def ClauseMatrix.pretty (matrix : ClauseMatrix) : String :=
  if matrix.isEmpty then "∅ (empty matrix)"
  else String.intercalate "\n" (matrix.toList.map Row.pretty)

/-- Pretty-print a decision tree.  Uses indentation for Switch
    subtrees so the branching structure is visible.  Accepts a
    base indent level so callers can nest cleanly. -/
partial def DecisionTree.prettyAt (indent : Nat) : DecisionTree → String
  | .leaf _ guard asBinds fallthrough _ =>
    let pad := String.ofList (List.replicate indent ' ')
    let guardPart :=
      match guard with
      | some _ => " if <guard>"
      | none   => ""
    let bindsPart :=
      if asBinds.isEmpty then ""
      else
        let pairs := asBinds.toList.map
          (fun (col, name) => s!"col{col}={name}")
        " [" ++ String.intercalate ", " pairs ++ "]"
    let fallthroughPart :=
      match fallthrough with
      | some sub =>
        "\n" ++ pad ++ "  fallthrough:\n"
          ++ DecisionTree.prettyAt (indent + 4) sub
      | none => ""
    s!"{pad}leaf: <body>{guardPart}{bindsPart}{fallthroughPart}"
  | .switch col specName branches fallbackBranch _ =>
    let pad := String.ofList (List.replicate indent ' ')
    let branchesPart := String.intercalate "\n"
      (branches.toList.map (fun (ctorIdx, sub) =>
        let subPad := String.ofList (List.replicate (indent + 4) ' ')
        let header := s!"{subPad}ctor#{ctorIdx}:"
        header ++ "\n" ++ DecisionTree.prettyAt (indent + 8) sub))
    let fallbackPart :=
      match fallbackBranch with
      | some sub =>
        let subPad := String.ofList (List.replicate (indent + 4) ' ')
        "\n" ++ subPad ++ "fallback:\n"
          ++ DecisionTree.prettyAt (indent + 8) sub
      | none => ""
    s!"{pad}switch col={col} on {specName}:\n{branchesPart}{fallbackPart}"
  | .fail witness _ =>
    let pad := String.ofList (List.replicate indent ' ')
    let wit := String.intercalate ", "
      (witness.toList.map prettyPattern)
    s!"{pad}fail: witness=[{wit}]"

/-- Top-level decision-tree pretty-printer; starts at indent 0. -/
def DecisionTree.pretty (tree : DecisionTree) : String :=
  DecisionTree.prettyAt 0 tree


/-! ## Smoke assertions (N3) — specialize / defaultMatrix

Build-time sanity checks for `specialize` and `defaultMatrix`.  If
either regresses, the build breaks.  These are minimal examples —
behavioral testing of the full Maranget pipeline lands at N12 via
the conformance suite. -/

namespace Smoke

private def smokeSpan : Span := Span.zero

private def qualZero : QualIdent :=
  { parts := #[], final := "Zero", span := smokeSpan }
private def qualSucc : QualIdent :=
  { parts := #[], final := "Succ", span := smokeSpan }

/-- Construct a Row with defaulted body/guard/asBinds fields. -/
private def smokeRow (armIdx : Nat) (pats : Array Pattern) : Row :=
  { patterns := pats
  , guard    := none
  , body     := Expr.unit smokeSpan
  , armIdx   := armIdx
  , asBinds  := #[]
  , span     := smokeSpan }

/-- S("Zero", 0) on [Zero; Succ(_); _] keeps the Zero row (pattern
    vector becomes empty) and the wildcard row (0 synthesized
    wildcards prepended to empty tail = empty).  Drops the Succ row. -/
example : (specialize "Zero" 0 #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan],
    smokeRow 2 #[Pattern.wildcard smokeSpan]
  ]).size = 2 := by native_decide

/-- S("Succ", 1) on the same matrix keeps the Succ row (its arg
    becomes col 0) and the wildcard row (one synthesized wildcard).
    Drops the Zero row. -/
example : (specialize "Succ" 1 #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan],
    smokeRow 2 #[Pattern.wildcard smokeSpan]
  ]).size = 2 := by native_decide

/-- S with no matching ctor rows and no catch-alls produces an empty
    matrix — the specialization hypothesizes "scrutinee head is c",
    but if no row accepts that case, the branch is dead. -/
example : (specialize "Succ" 1 #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan]
  ]).size = 0 := by native_decide

/-- D on a matrix with no catch-alls in col 0 is empty — no row
    accepts "head ctor is not in the explicit branch set". -/
example : (defaultMatrix #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan]
  ]).size = 0 := by native_decide

/-- D surfaces only catch-all rows (wildcard and var both count),
    dropping their column 0. -/
example : (defaultMatrix #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.wildcard smokeSpan],
    smokeRow 2 #[Pattern.var "n" smokeSpan]
  ]).size = 2 := by native_decide


/-! ### Compile smoke assertions (N4) -/

/-- A minimal CompileCtx for a Peano-Nat spec with Zero (arity 0,
    index 0) and Succ (arity 1 recursive, index 1).  Used by the
    N4 smoke assertions to exercise `compile` without pulling in
    the full elab pipeline. -/
private def natCtx : CompileCtx where
  lookupSpec
    | "Nat" => some #[
        { name := "Zero", arity := 0, argSpecs := #[],      ctorIndex := 0 },
        { name := "Succ", arity := 1, argSpecs := #["Nat"], ctorIndex := 1 }
      ]
    | _     => none

/-- Observe a DecisionTree's top-level shape as a Bool.  Keeps the
    smoke assertions `native_decide`-compatible. -/
private def isCompleteSwitch (expectedBranches : Nat)
    (tree : DecisionTree) : Bool :=
  match tree with
  | .switch _ _ branches fallback _ =>
    branches.size == expectedBranches && fallback.isNone
  | _ => false

private def isIncompleteSwitch (expectedBranches : Nat)
    (tree : DecisionTree) : Bool :=
  match tree with
  | .switch _ _ branches fallback _ =>
    branches.size == expectedBranches && fallback.isSome
  | _ => false

private def isLeaf (tree : DecisionTree) : Bool :=
  match tree with
  | .leaf _ _ _ _ _ => true
  | _               => false

/-- Match on Nat with exhaustive Zero + Succ(_) arms compiles to a
    Switch with two branches and no fallback.  Complete signature. -/
example : isCompleteSwitch 2 (compile natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan]
  ]) = true := by native_decide

/-- Match on Nat covering only Zero compiles to a Switch with one
    branch and a Some-fallback (the fallback compiles to Fail since
    Succ has no row to satisfy it — this is the non-exhaustive case
    N8 will report). -/
example : isIncompleteSwitch 1 (compile natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan]
  ]) = true := by native_decide

/-- Match on a single catch-all arm compiles directly to a Leaf —
    no ctor dispatch needed. -/
example : isLeaf (compile natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.wildcard smokeSpan]
  ]) = true := by native_decide

/-- Match where a wildcard row precedes a ctor row short-circuits to
    a Leaf: `compile` sees the head row is all catch-alls and emits
    the Leaf directly without examining the subsequent ctor row.
    The Zero arm is unreachable — N9's useless-clause detection will
    flag it later; N4 just produces a well-formed tree. -/
example : isLeaf (compile natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.wildcard smokeSpan],
    smokeRow 1 #[Pattern.ctor qualZero #[] smokeSpan]
  ]) = true := by native_decide


/-! ### Or-pattern expansion smoke assertions (N5) -/

/-- `expandPattern` on a bare `orPattern` flattens it into the
    alternative list. -/
example : (expandPattern (Pattern.orPattern #[
    Pattern.ctor qualZero #[] smokeSpan,
    Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan
  ] smokeSpan)).size = 2 := by native_decide

/-- Nested or inside a ctor arg: `Succ(Zero | _)` expands to two
    ctor patterns — `Succ(Zero)` and `Succ(_)`. -/
example : (expandPattern (Pattern.ctor qualSucc #[
    Pattern.orPattern #[
      Pattern.ctor qualZero #[] smokeSpan,
      Pattern.wildcard smokeSpan
    ] smokeSpan
  ] smokeSpan)).size = 2 := by native_decide

/-- Wildcard has exactly one "alternative" — itself. -/
example : (expandPattern (Pattern.wildcard smokeSpan)).size = 1 :=
  by native_decide

/-- The Q85+Q86 bug pattern: `Zero | Succ(Zero) | Succ(Succ(Zero))`
    as a single arm expands into THREE matrix rows, each carrying
    the same `armIdx`.  The legacy findSome? would have silently
    dropped two of them; N5 prevents this structurally. -/
example : (expandOrPatterns #[
    smokeRow 0 #[Pattern.orPattern #[
      Pattern.ctor qualZero #[] smokeSpan,
      Pattern.ctor qualSucc #[Pattern.ctor qualZero #[] smokeSpan] smokeSpan,
      Pattern.ctor qualSucc #[
        Pattern.ctor qualSucc #[Pattern.ctor qualZero #[] smokeSpan] smokeSpan
      ] smokeSpan
    ] smokeSpan]
  ]).size = 3 := by native_decide

/-- All three expanded rows from the above carry armIdx = 0 — the
    original source arm.  This is what makes N9 useless-clause
    detection attribute a dead arm back to ONE source location even
    when or-expansion multiplied it. -/
example :
    let expanded := expandOrPatterns #[
      smokeRow 0 #[Pattern.orPattern #[
        Pattern.ctor qualZero #[] smokeSpan,
        Pattern.ctor qualSucc #[Pattern.ctor qualZero #[] smokeSpan] smokeSpan
      ] smokeSpan]
    ]
    expanded.all (fun row => row.armIdx == 0) = true := by native_decide

/-- Matrix with no or-patterns passes through unchanged in row
    count. -/
example : (expandOrPatterns #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan],
    smokeRow 2 #[Pattern.wildcard smokeSpan]
  ]).size = 3 := by native_decide

/-- Cartesian product: a row with TWO or-patterns on separate
    columns expands to the product of their alternative counts. -/
example : (expandOrPatterns #[
    smokeRow 0 #[
      Pattern.orPattern #[Pattern.ctor qualZero #[] smokeSpan,
                         Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan] smokeSpan,
      Pattern.orPattern #[Pattern.wildcard smokeSpan,
                         Pattern.var "n" smokeSpan] smokeSpan
    ]
  ]).size = 4 := by native_decide


/-! ### As-pattern stripping smoke assertions (N6) -/

/-- `Zero as z` at col 0 strips to `Zero` with binding (0, z). -/
example :
    (stripAsFromRow (smokeRow 0 #[
      Pattern.asPattern (Pattern.ctor qualZero #[] smokeSpan) "z" smokeSpan
    ])).asBinds = #[(0, "z")] := by native_decide

/-- After strip, the pattern has NO asPattern wrapper remaining —
    `patternHasAnyAsPattern` returns false on the stripped col. -/
example :
    patternHasAnyAsPattern
      (stripAsFromRow (smokeRow 0 #[
        Pattern.asPattern (Pattern.ctor qualZero #[] smokeSpan) "z" smokeSpan
      ])).patterns[0]! = false := by native_decide

/-- Double-wrapped `(Zero as m) as n` peels recursively, inner
    first, outer last: binds = [(0, m), (0, n)]. -/
example :
    (stripAsFromRow (smokeRow 0 #[
      Pattern.asPattern
        (Pattern.asPattern (Pattern.ctor qualZero #[] smokeSpan) "m" smokeSpan)
        "n" smokeSpan
    ])).asBinds = #[(0, "m"), (0, "n")] := by native_decide

/-- Row without any as-patterns: asBinds remains empty after strip. -/
example :
    (stripAsFromRow (smokeRow 0 #[
      Pattern.ctor qualZero #[] smokeSpan
    ])).asBinds = #[] := by native_decide

/-- Matrix-level: strip runs per row, row count unchanged. -/
example :
    (stripAsFromMatrix #[
      smokeRow 0 #[Pattern.asPattern (Pattern.ctor qualZero #[] smokeSpan) "z" smokeSpan],
      smokeRow 1 #[Pattern.wildcard smokeSpan]
    ]).size = 2 := by native_decide

/-- `hasDeeplyNestedAsPattern` on a top-level `Zero as z`: false,
    this is N6's supported case. -/
example :
    hasDeeplyNestedAsPattern (Pattern.asPattern
      (Pattern.ctor qualZero #[] smokeSpan) "z" smokeSpan) = false :=
  by native_decide

/-- `hasDeeplyNestedAsPattern` on chained as `(Zero as m) as n`:
    false — both peel cleanly via `stripAsAtCol`. -/
example :
    hasDeeplyNestedAsPattern (Pattern.asPattern
      (Pattern.asPattern (Pattern.ctor qualZero #[] smokeSpan) "m" smokeSpan)
      "n" smokeSpan) = false := by native_decide

/-- `hasDeeplyNestedAsPattern` on `Succ(n as m)`: true — the as
    is inside a ctor arg, nested from the row-col perspective. -/
example :
    hasDeeplyNestedAsPattern (Pattern.ctor qualSucc #[
      Pattern.asPattern (Pattern.var "n" smokeSpan) "m" smokeSpan
    ] smokeSpan) = true := by native_decide

/-- `hasDeeplyNestedAsPattern` on `(Succ(n) as outer)`: false.  The
    outer `as` is top-level; its inner `Succ(n)` has no as-pattern,
    so chained or nested is irrelevant here. -/
example :
    hasDeeplyNestedAsPattern (Pattern.asPattern
      (Pattern.ctor qualSucc #[Pattern.var "n" smokeSpan] smokeSpan)
      "outer" smokeSpan) = false := by native_decide


/-! ### Guard handling smoke assertions (N7) -/

/-- A sentinel guard expression for smoke tests.  The actual guard
    contents don't matter for compile — N4 just wires the guard
    field through to the Leaf and records that fallthrough must
    exist; N10 lowers via `if guard then body else fallthrough`.
    Any non-`none` Expr suffices. -/
private def smokeGuard : Expr := Expr.unit smokeSpan

/-- Construct a smoke Row with a guard attached.  Body contents are
    irrelevant for compile — N4 only inspects patterns and guard —
    so the unit expression is reused. -/
private def smokeRowGuarded (armIdx : Nat) (pats : Array Pattern) : Row :=
  { patterns := pats
  , guard    := some smokeGuard
  , body     := Expr.unit smokeSpan
  , armIdx   := armIdx
  , asBinds  := #[]
  , span     := smokeSpan }

/-- Predicate: tree is a Leaf with `guard = some _` and
    `fallthrough = some _` — the invariant enforced by N4 on
    guarded leaves (N2 `DecisionTree.leaf` docstring). -/
private def isGuardedLeafWithFallthrough (tree : DecisionTree) : Bool :=
  match tree with
  | .leaf _ (some _) _ (some _) _ => true
  | _                             => false

/-- Predicate: tree is a Leaf with `guard = none` and
    `fallthrough = none` — the invariant for unguarded leaves. -/
private def isUnguardedLeaf (tree : DecisionTree) : Bool :=
  match tree with
  | .leaf _ none _ none _ => true
  | _                     => false

/-- Predicate: tree is a guarded Leaf whose fallthrough is Fail
    (i.e., no rows covered the guard's failure branch). -/
private def isGuardedLeafWithFailFallthrough (tree : DecisionTree) : Bool :=
  match tree with
  | .leaf _ (some _) _ (some ft) _ =>
    match ft with
    | .fail _ _ => true
    | _         => false
  | _                              => false

/-- Predicate: tree is a guarded Leaf whose fallthrough is another
    Leaf.  Used to verify `guarded head; unguarded tail` produces
    `Leaf guard (Leaf tail)` rather than `Leaf guard (Fail)`. -/
private def isGuardedLeafWithLeafFallthrough (tree : DecisionTree) : Bool :=
  match tree with
  | .leaf _ (some _) _ (some ft) _ =>
    match ft with
    | .leaf _ _ _ _ _ => true
    | _               => false
  | _                              => false

/-- Guarded catch-all with no tail: Leaf guard fallthrough=Fail.
    At runtime if the guard fails the match is non-exhaustive;
    N8 will flag it statically. -/
example : isGuardedLeafWithFailFallthrough (compile natCtx #["Nat"] #[
    smokeRowGuarded 0 #[Pattern.wildcard smokeSpan]
  ]) = true := by native_decide

/-- Guarded catch-all + unguarded catch-all fallthrough:
    `Leaf guard (Leaf)`.  The first arm fires when guard passes;
    the second arm catches the rest. -/
example : isGuardedLeafWithLeafFallthrough (compile natCtx #["Nat"] #[
    smokeRowGuarded 0 #[Pattern.wildcard smokeSpan],
    smokeRow 1 #[Pattern.wildcard smokeSpan]
  ]) = true := by native_decide

/-- Unguarded catch-all alone: Leaf with guard=none AND
    fallthrough=none (the invariant: unguarded leaves have dead
    fallthrough, correctly elided). -/
example : isUnguardedLeaf (compile natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.wildcard smokeSpan]
  ]) = true := by native_decide

/-- Guard on a ctor-specific row propagates through specialize.
    Matrix: `Succ(p) if guard => big; Succ(_) => other; Zero => z`.
    The Succ branch of the outer Switch compiles to a guarded Leaf
    (for "big") with Leaf fallthrough (for "other"); the Zero
    branch is an unguarded Leaf (for "z").  Tests the composition:
    specialize preserves the guard, base case 2 picks it up. -/
private def isSwitchWithGuardedSuccBranch (tree : DecisionTree) : Bool :=
  match tree with
  | .switch _ _ branches _ _ =>
    -- Succ has ctorIndex 1 in natCtx; look for that branch.
    match branches.find? (fun (idx, _) => idx == 1) with
    | some (_, succTree) => isGuardedLeafWithLeafFallthrough succTree
    | none               => false
  | _ => false

example : isSwitchWithGuardedSuccBranch (compile natCtx #["Nat"] #[
    smokeRowGuarded 0 #[Pattern.ctor qualSucc #[Pattern.var "p" smokeSpan] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan],
    smokeRow 2 #[Pattern.ctor qualZero #[] smokeSpan]
  ]) = true := by native_decide


/-! ### Exhaustiveness smoke assertions (N8) -/

/-- `useful(∅, [_])` — empty matrix, any value is useful.  The
    match `match n; end match;` with no arms is non-exhaustive. -/
example : useful natCtx #["Nat"] #[] #[Pattern.wildcard smokeSpan] = true
  := by native_decide

/-- `useful([Zero], [_])` — only Zero covered; a Succ value is
    useful.  Matches `match n; Zero => ...; end match;` — non-
    exhaustive. -/
example : useful natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan]
  ] #[Pattern.wildcard smokeSpan] = true := by native_decide

/-- `useful([Zero, Succ(_)], [_])` — exhaustive cover.  The
    wildcard query is NOT useful — no uncovered value exists. -/
example : useful natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan]
  ] #[Pattern.wildcard smokeSpan] = false := by native_decide

/-- `useful([_], [Zero])` — wildcard row covers Zero; not useful. -/
example : useful natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.wildcard smokeSpan]
  ] #[Pattern.ctor qualZero #[] smokeSpan] = false := by native_decide

/-- `useful([Zero], [Succ(_)])` — Succ(_) query; not covered by
    the Zero-only matrix; useful. -/
example : useful natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan]
  ] #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan] = true
  := by native_decide

/-- `useful([Zero], [Zero])` — exact-match row; not useful. -/
example : useful natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan]
  ] #[Pattern.ctor qualZero #[] smokeSpan] = false := by native_decide

/-- `isExhaustive` wrapper: empty matrix is non-exhaustive. -/
example : isExhaustive natCtx #["Nat"] #[] = false := by native_decide

/-- `isExhaustive` wrapper: Zero + Succ(_) covers Nat. -/
example : isExhaustive natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan]
  ] = true := by native_decide

/-- `isExhaustive` wrapper: only Zero — non-exhaustive (Succ
    uncovered). -/
example : isExhaustive natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan]
  ] = false := by native_decide

/-- `isExhaustive` wrapper: Zero + Succ(Zero) leaves Succ(Succ(_))
    uncovered — non-exhaustive.  This is the case that the Q85+Q86
    ad-hoc cascade used to silently accept; N8 via useful correctly
    flags it. -/
example : isExhaustive natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[
      Pattern.ctor qualZero #[] smokeSpan
    ] smokeSpan]
  ] = false := by native_decide

/-- `isExhaustive` wrapper: Zero + Succ(Zero) + Succ(_) IS
    exhaustive — the second Succ catches anything the first missed. -/
example : isExhaustive natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[
      Pattern.ctor qualZero #[] smokeSpan
    ] smokeSpan],
    smokeRow 2 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan]
  ] = true := by native_decide

/-- Catch-all covers everything after previous arms — exhaustive. -/
example : isExhaustive natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.wildcard smokeSpan]
  ] = true := by native_decide


/-! ### Useless-clause smoke assertions (N9) -/

/-- Empty matrix has no dead arms. -/
example : uselessArms natCtx #["Nat"] #[] = #[] := by native_decide

/-- Single arm is always reachable. -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.wildcard smokeSpan]
  ] = #[] := by native_decide

/-- `Zero => ...; _ => ...` — both reachable; no dead arms.  The
    wildcard catches Succ values, so it's useful against {Zero}. -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.wildcard smokeSpan]
  ] = #[] := by native_decide

/-- `_ => ...; Zero => ...` — wildcard first covers everything,
    so arm 1 (the Zero arm) is dead. -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.wildcard smokeSpan],
    smokeRow 1 #[Pattern.ctor qualZero #[] smokeSpan]
  ] = #[1] := by native_decide

/-- Redundant Zero: `Zero => ...; Zero => ...` — second Zero is
    dead (first already matches). -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualZero #[] smokeSpan]
  ] = #[1] := by native_decide

/-- `Zero => ...; Succ(_) => ...; _ => ...` — wildcard dead
    (exhaustive from first two arms). -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan],
    smokeRow 2 #[Pattern.wildcard smokeSpan]
  ] = #[2] := by native_decide

/-- Multiple dead arms reported in source order. -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.wildcard smokeSpan],
    smokeRow 1 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 2 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan]
  ] = #[1, 2] := by native_decide

/-- Or-pattern expansion: arm 0 has `Zero | Succ(_)` expanded to
    two rows (armIdx=0).  Arm 1 is `_`.  Arm 1 should be dead
    (arm 0 is exhaustive); arm 0 should be alive (at least one
    useful row).  Tests the per-ARM aggregation that distinguishes
    N9 from naive per-row checking. -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 0 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan],
    smokeRow 1 #[Pattern.wildcard smokeSpan]
  ] = #[1] := by native_decide

/-- Redundant or-alternatives within a single arm: `Zero | Zero`
    post-N5-expansion produces two rows with armIdx=0 both
    covering Zero.  The second row is per-row useless (covered by
    first), BUT the arm is alive (first row is useful).  N9
    returns empty — per-arm semantics wash out same-arm
    redundancy.  A finer pass could report "redundant alternative
    within arm 0" but that's out of N9 scope. -/
example : uselessArms natCtx #["Nat"] #[
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 0 #[Pattern.ctor qualZero #[] smokeSpan],
    smokeRow 1 #[Pattern.ctor qualSucc #[Pattern.wildcard smokeSpan] smokeSpan]
  ] = #[] := by native_decide


/-! ### Lowering dispatch smoke assertions (N10) -/

/-- Stub `LowerCtx` that returns identifiable sentinel Terms —
    `Term.var 0` for leaves, `Term.var 1` for switches, `Term.var 2`
    for guards, and `Except.error` for fail.  Tests verify
    `lowerDecisionTree` dispatches the right callback for each
    DecisionTree shape without depending on actual kernel term
    construction (which N11 owns). -/
private def stubLowerCtx : LowerCtx where
  emitLeaf _ _ _        := Except.ok (FX.Kernel.Term.var 0)
  emitSwitch _ _ _ _    := Except.ok (FX.Kernel.Term.var 1)
  emitGuard _ _ _ _     := Except.ok (FX.Kernel.Term.var 2)
  emitFail _ span       :=
    Except.error (ElabError.make "E010" "stub fail" span)

/-- Predicate: `Except ElabError Term` carries `Term.var n`. -/
private def isOkVar (index : Nat) : Except ElabError FX.Kernel.Term → Bool
  | Except.ok (FX.Kernel.Term.var n) => n == index
  | _                                 => false

/-- Lowering a Fail produces an error (routes to emitFail). -/
example : (lowerDecisionTree stubLowerCtx
    (DecisionTree.fail #[Pattern.wildcard smokeSpan] smokeSpan)).toBool = false
  := by native_decide

/-- Lowering an unguarded Leaf routes to emitLeaf → Term.var 0. -/
example : isOkVar 0 (lowerDecisionTree stubLowerCtx
    (DecisionTree.leaf (Expr.unit smokeSpan) none #[] none smokeSpan))
    = true := by native_decide

/-- Lowering a guarded Leaf with fallthrough routes to emitGuard →
    Term.var 2.  The whole guarded-leaf shape goes through
    emitGuard, which in the stub ignores its subterms. -/
example : isOkVar 2 (lowerDecisionTree stubLowerCtx
    (DecisionTree.leaf (Expr.unit smokeSpan) (some (Expr.unit smokeSpan))
      #[]
      (some (DecisionTree.leaf (Expr.unit smokeSpan) none #[] none smokeSpan))
      smokeSpan)) = true := by native_decide

/-- Lowering a guarded Leaf with MISSING fallthrough produces the
    internal-error E010 (N4 invariant violation check). -/
example : (lowerDecisionTree stubLowerCtx
    (DecisionTree.leaf (Expr.unit smokeSpan) (some (Expr.unit smokeSpan))
      #[] none smokeSpan)).toBool = false := by native_decide

/-- Lowering a Switch with empty branches + no fallback routes to
    emitSwitch → Term.var 1. -/
example : isOkVar 1 (lowerDecisionTree stubLowerCtx
    (DecisionTree.switch 0 "Nat" #[] none smokeSpan)) = true
  := by native_decide

/-- Lowering a Switch with one branch succeeds when the branch
    subtree also lowers (tests recursion through branches). -/
example : isOkVar 1 (lowerDecisionTree stubLowerCtx
    (DecisionTree.switch 0 "Nat" #[(0,
        DecisionTree.leaf (Expr.unit smokeSpan) none #[] none smokeSpan)]
      none smokeSpan)) = true := by native_decide

/-- Switch whose branch subtree is itself a Fail — error propagates
    up from the recursive call (tests monadic error threading
    through `Array.mapM`). -/
example : (lowerDecisionTree stubLowerCtx
    (DecisionTree.switch 0 "Nat" #[(0,
        DecisionTree.fail #[Pattern.wildcard smokeSpan] smokeSpan)]
      none smokeSpan)).toBool = false := by native_decide

end Smoke

end FX.Elab.Maranget
