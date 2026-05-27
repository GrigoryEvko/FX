import LeanFX2.Foundation.PolyCell.Core.GeneratorCore

/-! # Foundation/PolyCell/Core/GeneratorTotalityClassV2 — Turing-boundary classification

V2-L1.11 (2026-05-27).  Discharges polycell.md §11.7.2 "Turing's
ceiling → Tot/Div/Productive as Generator-level effect grades".
Ships the per-Generator `TotalityClass` classifier — the load-bearing
metadata that the future Tot/Productive/Partial fragment boundary
enforcement depends on.

## What this file ships

* **`TotalityClass`** — 3-ctor inductive: `totalClass`,
  `productiveClass`, `partialClass` (suffixed to avoid the Std.Total
  namespace collision and the Lean `partial` keyword).
* **`DecidableEq TotalityClass`** — needed for the certifier's
  per-child reconciliation.
* **`Generator.partialGenerators`** — exclusion list of generators
  whose untyped raw form may diverge (currently 2: `gen_natRec` and
  `gen_fixedPoint`).
* **`Generator.productiveGenerators`** — exclusion list of generators
  that produce non-terminating but observable structures (currently
  2: `gen_codataUnfold` and `gen_polyNu`).
* **`@[reducible] Generator.totalityClass`** — the dispatch.  Returns
  `partialClass` / `productiveClass` / `totalClass` based on
  list-membership.  Same architectural pattern as V2-fix-4's
  `coreFxExcluded` (`CoreFxProfile.lean`): list-based exclusion
  avoids a 194-arm match that would leak propext per Lean's
  match-equation-lemma discipline.

Eight witness theorems pin behavior on representative generators
across all three classes.

## The classification (current — defensible, conservative)

**partial (2 generators):**
* `gen_natRec` — general recursion on naturals; distinct from
  `gen_natElim` (primitive recursion = total).  Without an explicit
  termination measure, `natRec` may diverge.
* `gen_fixedPoint` — explicit Y-combinator-style fixed-point
  operator.  Fundamentally non-terminating without typing
  discipline.

**productive (2 generators):**
* `gen_codataUnfold` — codata stream/server constructor.  The
  produced structure is potentially infinite but every observation
  (head, tail-of-tail-of...) terminates.
* `gen_polyNu` — greatest fixpoint operator.  Coinductive type
  former; same productivity argument as `gen_codataUnfold`.

**total (190 generators):** every other generator in the 194-arm
table.  This includes:
* Lambda calculus core: `gen_var`, `gen_lam`, `gen_app`
* Primitive recursion: `gen_natElim`, `gen_listElim`, etc.
* Cubical: `gen_transp`, `gen_hcomp`, `gen_glueIntro`, etc.
* HITs: `gen_circleBase/Loop/Rec` — well-typed in HoTT, total.
* Categorical / modal / linear / etc.

## Why list-based dispatch (not 194-arm match)

A naive 194-arm `match gen with | .gen_var => .totalClass | ...`
would either:
1. Have 190 arms returning `.totalClass` (highly repetitive).
2. Use a wildcard `| _ => .totalClass` (LEAKS propext per
   `feedback_lean_zero_axiom_match` — match equation lemmas on
   inductives with >100 ctors trigger Lean's match-compiler
   propext path).

The list-based exclusion approach:
* 4 lines total (2 partial generators + 2 productive generators).
* `@[reducible]` on `totalityClass` makes the witness theorems
  close by `rfl` -- list-membership on a decidable-equality
  inductive reduces definitionally.
* Forward-compat: adding a new partial / productive generator
  is a list-append, not a 194-arm rewrite.

Same architectural pattern as V2-fix-4's `coreFxExcluded`
(restricted-profile admission predicate).  Both ship reusable
infrastructure that scales linearly with the exception count, not
with the generator count.

## What this enables

Per polycell.md §11.7.2:

> A `total` Generator's children must ALL be `total` (no Div child
>   in a Tot parent).
> A `productive` Generator may have `total` or `productive` children
>   (but not `partial`).
> A `partial` Generator may have children of any class.

The certifier's per-child reconciliation (`V2-L1cert.2`) will gain
a per-child `TotalityClass` check via this classification.  That
check ENFORCES the Turing-boundary structurally: every step of every
Tot/Productive cell tree carries a typed witness that no Partial
child has leaked into a Tot parent.

What this BUYS, per the spec:
* The Tot fragment is a DECIDABLE sub-language: SN holds (structural
  induction on total children gives termination), so NbE terminates,
  so Conv is decidable.
* The Productive fragment supports verified reactive systems: every
  observation reaches a value.
* The Partial fragment is Turing-complete: any computable function
  expressible, but the metatheory quartet does NOT hold for it.

## What's NOT shipped here

* **Certifier child-constraint enforcement** — requires extending
  `reconcileChildV2` (`V2-L1cert.2`) to check the child's
  TotalityClass against the parent's.  Deferred to a follow-up
  V2-L1.11.B if the certifier-side propagation lands.
* **The metatheory quartet on the Tot fragment** — SN + CR + SR +
  decidable Conv apply only after the certifier-side check is in
  place AND the L3 metatheory tasks land.
* **Profile-level subset/refinement of allowed TotalityClasses** —
  a restricted profile excluding the partial fragment would be a
  ProfileExtension follow-up.

## Forward-compat

When the certifier ships TotalityClass checking, this file's
exclusion lists become load-bearing.  Adding a new partial /
productive generator only requires editing the corresponding list
here -- the certifier inherits the updated boundary automatically.

## Zero-axiom verification

All 12 declarations pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.

## Ctor-naming discipline

The three TotalityClass constructors are suffixed `Class` because:
* `total` collides with `Std.Total.total` (Lean stdlib partial order
  total-relation).
* `partial` is a Lean keyword (modifier on `def`).
* `productive` -- no conflict, but suffixed for naming consistency
  across the three.

This is a localised naming workaround; user-facing FX code refers
to the totality classes via FX surface keywords (`with Tot`,
`with Div`, etc., per fx_design.md §1.1 Dimension 4 effects).
The Lean ctor names are an implementation detail of the metadata
table.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Three-way Turing-boundary classification of generator totality
behavior on UNTYPED raw inputs.  Suffixed `Class` to avoid Lean
stdlib namespace collisions and the `partial` keyword.

* `totalClass` -- always terminates; SN + CR + SR + decidable Conv
  hold structurally.
* `productiveClass` -- non-terminating but every observation
  terminates (codata streams, servers, reactive systems).
* `partialClass` -- may diverge; per-step SR holds, chain may be
  infinite. -/
inductive TotalityClass where
  | totalClass
  | productiveClass
  | partialClass
  deriving DecidableEq, Repr

namespace Generator

/-- Generators classified as `partialClass` (general recursion /
explicit fixed-point operator).

Currently 2: `gen_natRec` (general recursion on naturals; distinct
from `gen_natElim`'s primitive recursion) and `gen_fixedPoint`
(explicit Y-combinator-style operator).  Adding a new partial
generator only requires appending here. -/
def partialGenerators : List Generator :=
  [.gen_natRec, .gen_fixedPoint]

/-- Generators classified as `productiveClass` (codata producers /
greatest fixpoint operators).

Currently 2: `gen_codataUnfold` (stream/server constructor with
finite observations) and `gen_polyNu` (greatest fixpoint operator
for coinductive types). -/
def productiveGenerators : List Generator :=
  [.gen_codataUnfold, .gen_polyNu]

/-- Look up the totality class for a generator.  Returns
`partialClass` / `productiveClass` / `totalClass` based on
list-membership against `partialGenerators` and `productiveGenerators`.

Defaults to `totalClass` for any generator not in either exclusion
list (190 of the 194 V2 generators).

The `@[reducible]` attribute makes the witness theorems below close
by `rfl` -- list-membership on a decidable-equality inductive
reduces definitionally. -/
@[reducible] def totalityClass (gen : Generator) : TotalityClass :=
  if partialGenerators.contains gen then .partialClass
  else if productiveGenerators.contains gen then .productiveClass
  else .totalClass

end Generator

/-! ## Witness theorems (8 representative generators across all 3 classes)

These theorems pin the classifier's behavior on representative
generators.  Each closes by `rfl` because `@[reducible]` on
`totalityClass` unfolds list-membership at typecheck time.

A regression that incorrectly added a generator to one of the
exclusion lists, or that changed the default branch from
`totalClass`, would fail one of these witnesses. -/

theorem gen_var_total :
    Generator.totalityClass .gen_var = .totalClass := rfl

theorem gen_unit_total :
    Generator.totalityClass .gen_unit = .totalClass := rfl

theorem gen_natElim_total :
    Generator.totalityClass .gen_natElim = .totalClass := rfl

theorem gen_codataDest_total :
    Generator.totalityClass .gen_codataDest = .totalClass := rfl

theorem gen_natRec_partial :
    Generator.totalityClass .gen_natRec = .partialClass := rfl

theorem gen_fixedPoint_partial :
    Generator.totalityClass .gen_fixedPoint = .partialClass := rfl

theorem gen_codataUnfold_productive :
    Generator.totalityClass .gen_codataUnfold = .productiveClass := rfl

theorem gen_polyNu_productive :
    Generator.totalityClass .gen_polyNu = .productiveClass := rfl

end LeanFX2.Foundation.PolyCell.Core
