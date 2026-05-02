import LeanFX2.Foundation.Interval

/-! # Foundation/Cofib — boundary face cofibrations for cubical Glue/comp

A cofibration is a face condition on the interval — a propositional
formula in `i = i0` and `i = i1` connectives.  CCHM cubical type theory
uses an arbitrary cofibration lattice; for v1.0 we ship the
**boundary-only** fragment, which is sufficient for Glue/ua and most
practical path operations.

## What v1.0 ships

`BoundaryCofib` enum with 4 cases:

* `atZero`     — face holds when `i = i0`
* `atOne`      — face holds when `i = i1`
* `atBoth`     — face holds at both endpoints (always-true at boundary)
* `atNeither`  — face never holds (used for trivial Glue construction)

The general face lattice (with arbitrary `i = i0 ∨ j = i1` etc.) is v1.1.

## Predicate `holds`

`BoundaryCofib.holds : BoundaryCofib → Interval → Bool` decides whether
a given cofibration is satisfied at a given interval point.  Total,
decidable, full enumeration (no wildcards).

## Decidability

Both `BoundaryCofib` and `Interval` have `DecidableEq`, so `holds`
returns `Bool` directly.

## Pitfalls

* P-1 (match-compiler propext): every match is full enumeration.
* Per `feedback_lean_match_propext_recipe`, wildcards over big inductives
  leak propext.  We have only 4 ctors here so wildcards would be safe,
  but discipline is uniform.

## Downstream consumers

* `Foundation/Ty.lean` — `Ty.glue (A : Ty level scope) (cofib : BoundaryCofib) ...`
* `Cubical/Composition.lean` — comp/hcomp at boundary
* `Cubical/Glue.lean` — Glue construction restricted to boundary cofibs
* `Cubical/Ua.lean` — ua via Glue uses `atBoth` cofibration
-/

namespace LeanFX2

/-- Boundary face cofibrations — sufficient for Glue + ua + boundary
path operations.  General face lattice (CCHM-style with arbitrary
∨/∧ of `i = e`) is v1.1. -/
inductive BoundaryCofib : Type
  /-- Face condition `i = i0`. -/
  | atZero : BoundaryCofib
  /-- Face condition `i = i1`. -/
  | atOne : BoundaryCofib
  /-- Face holds at both endpoints (always at boundary). -/
  | atBoth : BoundaryCofib
  /-- Face never holds (degenerate; trivial Glue). -/
  | atNeither : BoundaryCofib
  deriving DecidableEq, Repr

/-- Whether a cofibration holds at a given interval point.
Full enumeration of all 8 (cofib, point) pairs — no wildcards. -/
def BoundaryCofib.holds : BoundaryCofib → Interval → Bool
  | .atZero, .i0 => true
  | .atZero, .i1 => false
  | .atOne, .i0 => false
  | .atOne, .i1 => true
  | .atBoth, .i0 => true
  | .atBoth, .i1 => true
  | .atNeither, .i0 => false
  | .atNeither, .i1 => false

/-- `atBoth` always holds. -/
theorem BoundaryCofib.atBoth_always (i : Interval) :
    BoundaryCofib.atBoth.holds i = true := by
  cases i <;> rfl

/-- `atNeither` never holds. -/
theorem BoundaryCofib.atNeither_never (i : Interval) :
    BoundaryCofib.atNeither.holds i = false := by
  cases i <;> rfl

/-- `atZero` at `i0`. -/
theorem BoundaryCofib.atZero_at_i0 :
    BoundaryCofib.atZero.holds Interval.i0 = true := rfl

/-- `atZero` not at `i1`. -/
theorem BoundaryCofib.atZero_not_at_i1 :
    BoundaryCofib.atZero.holds Interval.i1 = false := rfl

/-- `atOne` not at `i0`. -/
theorem BoundaryCofib.atOne_not_at_i0 :
    BoundaryCofib.atOne.holds Interval.i0 = false := rfl

/-- `atOne` at `i1`. -/
theorem BoundaryCofib.atOne_at_i1 :
    BoundaryCofib.atOne.holds Interval.i1 = true := rfl

end LeanFX2
