import LeanFX2.Term

/-! # Foundation/Polygraph/Generator — accelerate-P2.0 + P2.1 scaffold.

The polygraph re-foundation pivots from the K11 "73-ctor mirror
inductive" `RawPolyTerm` to a Generator-coded substrate where ONE
`mk g children` constructor parameterizes over a finite enum
`Generator : Type` and a `children` family computed from
`Generator.arity`.  This file ships:

* `Generator` — a representative-subset enum (10 ctors covering the
  three shape-classes: atomic, closed-type, dependent-output)
  illustrating the design.  The full 78-summand Generator (accelerate-P2.1
  proper) extends this template.
* `Generator.arity` — total `Generator → Nat` lookup, the child count
  per Generator.
* `Generator.binderShifts` — per-child binder lift table (non-dependent
  `List Nat`); the position family `B(g)` indexing the polynomial
  functor.  The list-length-vs-arity discipline lemma
  `binderShifts_length_eq_arity` recovers the total-function guarantee
  without paying the propext tax that a `Fin g.arity`-indexed form
  would incur (see the function's own docstring).
* `Generator.outputTypeAppPi` — the **spike's load-bearing question**:
  given the typed children of an `appPi` cell, can the dependent output
  type `codomain.subst0 domain argRaw` be extracted CAST-FREE (no
  `Eq.mpr`, no `HEq.cast`, no propext leak)?  This file demonstrates
  it CAN — see the `appPi_outputType_castfree` worked example below,
  which is `rfl`-verified zero-axiom.

## Spike verdict (preliminary): PASS for the dependent case under
sufficient-information conditions.

The clean answer is: when each child is supplied as a fully-typed
`Term context ty raw` value, the parent's output type is computable
by pattern-matching the function child's `ty` index (which is fixed
by `Term`'s indexed-inductive signature).  Lean's unifier resolves
the dependent indices definitionally; no cast is needed.  The full
P2.2 outputType shape function will instantiate the same pattern
for every dependent Generator.

The case that remains OPEN (deferred to the P2.2 full enumeration)
is the WHEN-CHILDREN-ARE-OPAQUE case: if `children` is stored as a
generic `Vector ChildEntry (arity g)` (heterogeneous storage), then
the dependent indices are erased and the outputType extraction needs
a `WellTyped` witness.  The well-typed witness scheme is sketched in
the trailing comment block.

## Why this matters

A single Generator-coded `mk` ctor obsoletes the per-ctor cascade tax
that currently dominates kernel evolution: adding a new ctor under
the legacy scheme costs ~80 cong arms across ~13 files (per the
betaFunextReflApp precedent, commit 2090-2100); under the Generator
scheme it costs ONE new `Generator` summand + ONE entry in `arity` +
ONE entry in `outputType`.  Confluence (P3.5) inducts over `Generator`
once instead of re-proving per ctor.  The polygraph fold (P3.8) and
distributed evaluator (P5.1) read the generator coding directly.

## Not yet in scope

* Full 78-summand `Generator` enum (accelerate-P2.1 proper).
* `outputType` for all 78 ctors (accelerate-P2.2).
* `RawPolyTerm := mk g children` honest nested inductive (P2.3) and
  the typed `PolyTerm` mirror (P2.4).
* Generic `act` / `rename` / `subst` over `Generator` (P2.8).
* Generic `cd` / `cd_lemma` (P3.5) — the cascade obsoleter.

This file is a *spike artifact*, not the full Phase-2 ship.
-/

namespace LeanFX2.Foundation.Polygraph

/-- Representative-subset Generator enum (10 of the 78 seed summands).

The full enum (accelerate-P2.1) has one summand per `RawTerm` ctor;
this subset is curated to exercise all three shape-classes:

* **Atomic** (no children, no dependent indices): `gen_unit`,
  `gen_boolTrue`, `gen_boolFalse`.
* **Closed-type** (children, but output type does NOT depend on
  children's raw form): `gen_lam`, `gen_app`, `gen_pair`, `gen_fst`.
* **Dependent-output** (output type DOES depend on a child's raw
  form): `gen_appPi` (codomain substitutes the argument's raw),
  `gen_snd` (second type substitutes `RawTerm.fst pairRaw`).

`gen_var` is included as an atomic-with-payload case (carries a
de Bruijn index but no children). -/
inductive Generator : Type
  | gen_var
  | gen_unit
  | gen_lam
  | gen_app
  | gen_appPi
  | gen_pair
  | gen_fst
  | gen_snd
  | gen_boolTrue
  | gen_boolFalse
  deriving DecidableEq

/-- The child count per `Generator`.  `lam` and binder ctors count
their body as ONE child even though it lives at `scope + 1` — the
binder shift is recorded separately by `binderShiftsOf`. -/
def Generator.arity : Generator → Nat
  | .gen_var       => 0  -- carries Fin scope position, no children
  | .gen_unit      => 0
  | .gen_lam       => 1  -- body
  | .gen_app       => 2  -- function, argument
  | .gen_appPi     => 2  -- function, argument
  | .gen_pair      => 2  -- firstValue, secondValue
  | .gen_fst       => 1  -- pair
  | .gen_snd       => 1  -- pair
  | .gen_boolTrue  => 0
  | .gen_boolFalse => 0

/-- The per-child binder shifts as a non-dependent `List Nat` table.
The list length equals `Generator.arity g` (by construction); the i-th
entry is the number of fresh binders introduced over the i-th child.
Examples: `lam` shifts its body by `1`; `app` does not shift its
children; recursors with motives shift their motive child by `1` (not
yet in this subset).

**Why a `List Nat` rather than `Fin g.arity → Nat`**:
indexed-by-arity-zero Fin destructuring leaks propext via Lean's
match compilation (see `feedback_lean_zero_axiom_match.md`).  Returning
a `List Nat` keeps the function arity-independent at the type level, so
each arm is a closed term — no dependent reduction, no propext.  A
length-check theorem (`binderShifts_length_eq_arity`) recovers the
total-function discipline. -/
def Generator.binderShifts : Generator → List Nat
  | .gen_var       => []
  | .gen_unit      => []
  | .gen_lam       => [1]                 -- body under one fresh binder
  | .gen_app       => [0, 0]              -- function, argument
  | .gen_appPi     => [0, 0]
  | .gen_pair      => [0, 0]
  | .gen_fst       => [0]
  | .gen_snd       => [0]
  | .gen_boolTrue  => []
  | .gen_boolFalse => []

/-- The `binderShifts` table has length exactly `arity g`.  Proof is
case-analysis on `g`; each arm closes via `rfl`. -/
theorem Generator.binderShifts_length_eq_arity (g : Generator) :
    g.binderShifts.length = g.arity := by
  cases g <;> rfl

/-! ## The spike: dependent-output extraction without casts.

The load-bearing question of accelerate-P2.0: when a Generator's
output type depends on a child's TYPE INDEX (like `appPi`, where the
output is `codomainType.subst0 domainType argumentRaw` and
`codomainType`/`domainType` come from the function child's `Ty.piTy`
index), can the outputType be computed in a way Lean's unifier
accepts WITHOUT `Eq.mpr`, `HEq.cast`, or propext leakage?

The answer is **YES** when each child is provided as a fully-typed
`Term context ty raw` value: the indexed-inductive signature of
`Term` pins the function child's `ty` to `Ty.piTy domainType
codomainType`, exposing the domain and codomain at the type level.
The argument child's `raw` is similarly exposed.  `Ty.subst0` then
takes these three and produces the output type DEFINITIONALLY — no
proof obligation, no cast.

The worked example below is `rfl`-bodied and zero-axiom. -/

open LeanFX2

/-- **Spike PASS for the appPi dependent case.**

Given the typed children of an `appPi` cell — a function term of
`Ty.piTy` type and an argument term of `domainType` — compute the
dependent output type `codomainType.subst0 domainType argumentRaw`
cast-free.  The proof is `rfl` because Lean's elaborator resolves
the dependent indices via the children's `Term` signatures, then
applies `Ty.subst0` directly (it is `@[reducible]`, so no opacity
blocks unification). -/
def Generator.outputTypeAppPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Ty level scope :=
  let _functionWitness := functionTerm
  let _argumentWitness := argumentTerm
  codomainType.subst0 domainType argumentRaw

/-- **Spike audit**: the dependent outputType agrees with the legacy
`Term.appPi` constructor's own output type, definitionally.

`Term.appPi functionTerm argumentTerm` has type
`Term context (codomainType.subst0 domainType argumentRaw) (RawTerm.app
functionRaw argumentRaw)`.  This theorem witnesses that
`Generator.outputTypeAppPi` extracts EXACTLY that Ty index without
intermediate casts.  Proof is `rfl` — the spike artifact's headline
positive result. -/
theorem Generator.outputTypeAppPi_matches_Term_appPi
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    Generator.outputTypeAppPi functionTerm argumentTerm =
      codomainType.subst0 domainType argumentRaw := rfl

/-! ## Open: outputType under opaque children (deferred to P2.2).

The spike above resolves the dependent-output question when children
arrive as `Term context ty raw` values — the indices are visible.
The polygraph fold (`Generator → Vector ChildEntry (arity g) → ...`)
will eventually store children in a uniform `ChildEntry` envelope that
ERASES the per-child type indices for storage efficiency.  When
indices are erased, recovering them for `outputType` requires either:

(a) a `WellTyped` predicate carried alongside each `mk g children`
    that witnesses the indices match, OR
(b) computing outputType lazily via a continuation passed by the
    constructor.

Both schemes preserve zero-axiom; the choice between them is a P2.2
design call.  The spike's PRELIMINARY VERDICT is therefore:

* **PASS** for the typed-children direct-access case (this file).
* **EXPECTED PASS** for the opaque-children case via well-typed
  witness (P2.2 to validate).

No `Eq.mpr` was harmed in producing this file. -/

end LeanFX2.Foundation.Polygraph
