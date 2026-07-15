import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Frontier.ModeOmegaWeakGray

/-! # FX1PolyAudit/AuditAxisModeFrontierModeOmegaWeakGray — zero-axiom gate for the mode-21 frontier narrows

Per-declaration zero-axiom gate for `FX1Poly/Axis/Mode/Frontier/ModeOmegaWeakGray.lean` — the genuine content
NARROWING two `ModeOmega` capstone markers:

  * marker 1 (`fxMode_hasModeOmegaWeakGray`): the Type-valued (codiscrete) dim-3 cell structure
    (`codiscreteGrayCategory`), the concrete lawful non-subsingleton-2-cell base (`boolEndoTwoCategory`), and the
    weak-coherence 3-cell between provably-distinct parallel 2-cells (`boolEndoWeakCoherenceCell`), plus the
    Eckmann–Hilton honesty payload;
  * marker 2 (`fxMode_hasModeOmegaCanonicityTransport`): the canonicity-of-2-cells fragment
    (`TwoCellCanonicity`, `DecidableTwoCellEquality.canonicity`, `strictTwoCellCanonicity`) — canonical forms
    exist + are unique + decide equality.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Marker 1: the codiscrete (Type-valued) dim-3 cell structure
#assert_no_axioms FX1Poly.Axis.codiscreteGrayCategory
#assert_no_axioms FX1Poly.Axis.codiscreteGrayCategory_twoCategory
#assert_no_axioms FX1Poly.Axis.codiscreteGrayCategory_threeCell_isUnit

-- Marker 1: the concrete lawful base 2-category with genuinely non-subsingleton 2-cells
#assert_no_axioms FX1Poly.Axis.pointCategory
#assert_no_axioms FX1Poly.Axis.pointObject
#assert_no_axioms FX1Poly.Axis.pointHom
#assert_no_axioms FX1Poly.Axis.boolEndoTwoCategory
#assert_no_axioms FX1Poly.Axis.boolEndoTwoCell
#assert_no_axioms FX1Poly.Axis.boolEndoTwoCategory_hasDistinctParallelTwoCells
#assert_no_axioms FX1Poly.Axis.boolEndoTwoCategory_interchange_orders_agree

-- Marker 1: the weak-coherence 3-cell between provably-distinct parallel 2-cells (the teeth)
#assert_no_axioms FX1Poly.Axis.boolEndoWeakCoherenceCell
#assert_no_axioms FX1Poly.Axis.boolEndoWeakCoherenceCell_boundary_isNonIdentity
#assert_no_axioms FX1Poly.Axis.boolEndoGrayCategory_interchanger_isUnit

-- Marker 2: the canonicity-of-2-cells fragment
#assert_no_axioms FX1Poly.Axis.TwoCellCanonicity
#assert_no_axioms FX1Poly.Axis.DecidableTwoCellEquality.canonicity
#assert_no_axioms FX1Poly.Axis.TwoCellCanonicity.equal_self
#assert_no_axioms FX1Poly.Axis.TwoCellCanonicity.equal_iff_canonicalForm
#assert_no_axioms FX1Poly.Axis.strictTwoCellCanonicity
#assert_no_axioms FX1Poly.Axis.strictTwoCellCanonicity_canonicalForm_id
#assert_no_axioms FX1Poly.Axis.strictTwoCellNormalForm_exhaustive
#assert_no_axioms FX1Poly.Axis.strictTwoCellCanonicity_discriminates
#assert_no_axioms FX1Poly.Axis.strictTwoCellCanonicity_equal_iff_eq

-- Bundling the weak-Gray scaffolding + 2-cell canonicity INTO the ModeOmega capstone (the marker flips)
#assert_no_axioms FX1Poly.Axis.ModeOmega.grayCategory
#assert_no_axioms FX1Poly.Axis.ModeOmega.grayCategory_twoCategory
#assert_no_axioms FX1Poly.Axis.ModeOmega.contractibleGlobularSkeleton
#assert_no_axioms FX1Poly.Axis.ModeOmega.semistrictSignature
#assert_no_axioms FX1Poly.Axis.ModeOmega.twoCellCanonicity
#assert_no_axioms FX1Poly.Axis.ModeOmega.twoCell_equal_iff_canonicalForm

end FX1PolyAudit
