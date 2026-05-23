import LeanFX2.Foundation.Polygraph.RawPolyTermFlat
import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.StrictHarness.TrustEscape

/-! # AuditRawPolyTermFlat — zero-axiom audit for the polygraph
substrate (accelerate-P2.3 / #2124).

Smoke gates for the honest nested inductive that replaces the
74-summand `RawPolyTerm` mirror.  After this ship lands:

* `Generator.payload : Generator → Nat → Type` returns one of three
  payload shapes (`Fin scope` for var, `Nat` for universeCode, `Unit`
  for the remaining 72).
* `RawPolyTermFlat : Nat → Type` carries the polygraph substrate via
  ONE `mk` constructor instead of 74.
* `RawPolyTermFlatChildren : List Nat → Nat → Type` is the children
  list indexed by binder-shift table.
* Five definitional aliases (`empty` / `single` / `singleUnderBinder`
  / `pairFlat` / `binderShape` / `tripleFlat`) cover all observed
  arity-shift shapes in the 74-ctor table.

## Coverage

The smoke gates here verify ONLY that the substrate type-checks and
introduces no axioms.  Bijection + roundtrip with the legacy
`RawPolyTerm` (P2.5) and PolyTerm integration (P2.4) ship in
follow-up slices.

## Bijection foundation

The honest-nested form is the substrate for everything downstream:

* P2.4 — `PolyTerm` indexed by `RawPolyTermFlat` (one mk ctor instead
  of 74).
* P2.5 — `PolyTerm.toRawPoly_rfl` free erasure via the bijection.
* P2.8 — `PolyTerm.rename` / `PolyTerm.subst` as ONE generic
  `Generator → ...` fold instead of 74 per-ctor arms.
* P3.5 — `PolyStep.cd` / `cd_lemma` generic over `Generator`,
  obsoleting the D2.5.x per-arm cascades. -/

namespace LeanFX2.SmokeRawPolyTermFlat

#assert_no_axioms LeanFX2.Foundation.Polygraph.Generator.payload

#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.empty
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.single
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.singleUnderBinder
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.pairFlat
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.binderShape
#assert_no_axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.tripleFlat

#print axioms LeanFX2.Foundation.Polygraph.Generator.payload
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlat
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.empty
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.single
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.singleUnderBinder
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.pairFlat
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.binderShape
#print axioms LeanFX2.Foundation.Polygraph.RawPolyTermFlatChildren.tripleFlat

end LeanFX2.SmokeRawPolyTermFlat
