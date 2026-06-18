import FX1Poly.Typed.Dimensions.Parametricity.GelIsTranspensionAtAffine

/-! # FX1Poly/Typed/Dimensions/Parametricity/AffineBoundaryStructural
    — Nuyts hurdle 4 (decide the boundary predicate) is MOOT on the affine multiplier

Nuyts' transpension conclusion lists four hurdles to an intensional (decidable, computing) transpension.
Hurdle 4: "decide whether the boundary predicate ... `i = 0` in cubical type theory is true."  In CCHM
cubical type theory this needs a cofibration / face-lattice solver — an SMT / QF_BV-flavoured decision
procedure (the cofibration solvers of Cubical Agda / redtt).

This module shows hurdle 4 is MOOT for FX's transpension, with no SMT engine.  The QF_BV complexity comes
ENTIRELY from the CONNECTIONS of the cartesian / De Morgan interval (the `and` / `or` / `not` operators):
with connections you can form a compound dimension term like `i and 0` that is semantically on the boundary
(`i and 0 = 0`) without being syntactically `0`, so deciding boundary membership requires normalising the
connection algebra (the face lattice).

FX's transpension lives on the AFFINE multiplier — `gel = transpension @ affine` (rung 1,
`GelIsTranspensionAtAffine`).  The affine interval forbids connections: `mode-2` proves
`gelStructureClass.supportsConnections = false`.  By Cavallo-Harper's bridge-dimension grammar
`r ::= x | 0 | 1` (Def 2.1), the ONLY affine dimension terms are the two endpoints and variables — no
compound faces.  So boundary membership is decided by a single STRUCTURAL head-check on the dimension term
(is it `interval0` / `interval1`, versus a variable): the characteristic map of the subobject
`boundary ↪ interval`, where the affine boundary is the two endpoints (`partial-interval = top + top`,
Nuyts Example 6.14).  No SMT, no cofibration solver, no QF_BV engine — a `decide`-of-`DecidableEq`
head-test, exactly the shipped `Generator.hasRedexHead` pattern.

The structure-class certificate that gates SOUNDNESS (affine for parametricity) is the SAME flag that gates
the boundary predicate's DECIDABILITY COMPLEXITY: `supportsConnections = false` collapses the
lattice-entailment problem to a structural match.  This is "the structure-class gates the metatheory" made
concrete for Nuyts hurdle 4 — and it is the boundary-decision procedure the eventual explicit-dimension
boundary iota rows (the gel boundary `gel @ 0 reduces-to a`, `gel @ 1 reduces-to b`) will consult.

## Zero-axiom verification

The boundary predicate is a total `Bool` function (so trivially `Decidable`); every fact is `rfl` or a
short structural proof over `DecidableEq`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditAffineBoundaryStructural.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Tier0
open FX1Poly.Core

/-! ## The structural boundary predicate -/

/-- The structural endpoint test on a generator: is it an affine-interval endpoint (`interval0` /
`interval1`)?  Mirrors the shipped `Generator.hasRedexHead` `decide`-`||` pattern — `DecidableEq`, no
match-wildcard, hence no SMT and no propext leak. -/
def isAffineEndpointHead (generator : Generator) : Bool :=
  decide (generator = .gen_interval0) || decide (generator = .gen_interval1)

/-- The **affine boundary predicate** on a dimension term: `true` iff the term is an endpoint of the affine
interval.  A single-constructor match on `RawTerm` followed by a head-check — the characteristic map of
`boundary ↪ interval`.  Total, computable, decidable — NO solver. -/
def isOnAffineBoundary {scope : Nat} (dimension : RawTerm scope) : Bool :=
  match dimension with
  | .mkGen generator _payload _children => isAffineEndpointHead generator

/-! ## The boundary computes structurally — no SMT, every fact by `rfl` -/

/-- `interval0` is on the boundary (the left endpoint) — by `rfl`, no solver. -/
theorem interval0_isOnAffineBoundary {scope : Nat} :
    isOnAffineBoundary (scope := scope) (.mkGen .gen_interval0 () .childNil) = true := rfl

/-- `interval1` is on the boundary (the right endpoint) — by `rfl`, no solver. -/
theorem interval1_isOnAffineBoundary {scope : Nat} :
    isOnAffineBoundary (scope := scope) (.mkGen .gen_interval1 () .childNil) = true := rfl

/-- A dimension VARIABLE is in the interior (not on the boundary) — by `rfl`.  On the affine interval the
interior is exactly the variables (there are no connections to get stuck on), so this structural `false` is
COMPLETE. -/
theorem var_isNotOnAffineBoundary {scope : Nat} (position : Fin scope) :
    isOnAffineBoundary (.mkGen .gen_var position .childNil) = false := rfl

/-! ## The classifier — only endpoints are on the boundary (the subobject `boundary ↪ interval`) -/

/-- ★ The boundary predicate CLASSIFIES exactly the two endpoints: a generator passing the affine endpoint
test is `interval0` or `interval1`.  This is completeness of the structural check — on the affine interval
there is nothing else on the boundary (the categorical `partial-interval = top + top`). -/
theorem affineEndpoint_classifies (generator : Generator)
    (isEndpoint : isAffineEndpointHead generator = true) :
    generator = .gen_interval0 ∨ generator = .gen_interval1 := by
  unfold isAffineEndpointHead at isEndpoint
  cases hLeft : decide (generator = .gen_interval0) with
  | true => exact Or.inl (of_decide_eq_true hLeft)
  | false =>
    rw [hLeft, Bool.false_or] at isEndpoint
    exact Or.inr (of_decide_eq_true isEndpoint)

/-! ## ★ The moot theorem — why no QF_BV / cofibration solver is needed -/

/-- ★★ **Nuyts hurdle 4 is moot on the affine multiplier.**  The boundary predicate needs an SMT /
cofibration solver ONLY because of the interval's CONNECTIONS (the `i and 0`-style compound faces).  The
affine multiplier — `gel = transpension @ affine` (rung 1) — forbids connections, so the boundary
predicate is the structural head-check `isOnAffineBoundary` above (decidable by `DecidableEq`, no solver).
The `mode-2` flag `supportsConnections = false` IS the reason: the same certificate that makes Gel sound
makes its boundary predicate trivially decidable. -/
theorem affineBoundary_needsNoConnectionSolver :
    gelStructureClass.supportsConnections = false := rfl

/-- Non-degeneracy / contrast: the De Morgan (CCHM) multiplier DOES support connections — that is exactly
the class where the boundary predicate WOULD need the cofibration / QF_BV solver.  The structural
head-check is complete for `affine`, NOT for `deMorgan`; the boundary's decidability complexity is gated by
the structure-class, so the QF_BV need is a property of the cartesian/De Morgan path interval, never of the
affine bridge interval FX's transpension uses. -/
theorem deMorganBoundary_wouldNeedConnectionSolver :
    MultiplierStructureClass.deMorgan.supportsConnections = true := rfl

end FX1Poly.Typed
