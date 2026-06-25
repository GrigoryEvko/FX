import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Frontier.ModeOmegaWeakGray

/-! # FX1PolyAudit/AuditTier0ModeFrontierModeOmegaWeakGray — zero-axiom gate for the mode-21 frontier narrows

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Mode/Frontier/ModeOmegaWeakGray.lean` — the genuine content
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
#assert_no_axioms FX1Poly.Tier0.codiscreteGrayCategory
#assert_no_axioms FX1Poly.Tier0.codiscreteGrayCategory_twoCategory
#assert_no_axioms FX1Poly.Tier0.codiscreteGrayCategory_threeCell_isUnit

-- Marker 1: the concrete lawful base 2-category with genuinely non-subsingleton 2-cells
#assert_no_axioms FX1Poly.Tier0.pointCategory
#assert_no_axioms FX1Poly.Tier0.pointObject
#assert_no_axioms FX1Poly.Tier0.pointHom
#assert_no_axioms FX1Poly.Tier0.boolEndoTwoCategory
#assert_no_axioms FX1Poly.Tier0.boolEndoTwoCell
#assert_no_axioms FX1Poly.Tier0.boolEndoTwoCategory_hasDistinctParallelTwoCells
#assert_no_axioms FX1Poly.Tier0.boolEndoTwoCategory_interchange_orders_agree

-- Marker 1: the weak-coherence 3-cell between provably-distinct parallel 2-cells (the teeth)
#assert_no_axioms FX1Poly.Tier0.boolEndoWeakCoherenceCell
#assert_no_axioms FX1Poly.Tier0.boolEndoWeakCoherenceCell_boundary_isNonIdentity
#assert_no_axioms FX1Poly.Tier0.boolEndoGrayCategory_interchanger_isUnit

-- Marker 2: the canonicity-of-2-cells fragment
#assert_no_axioms FX1Poly.Tier0.TwoCellCanonicity
#assert_no_axioms FX1Poly.Tier0.DecidableTwoCellEquality.canonicity
#assert_no_axioms FX1Poly.Tier0.TwoCellCanonicity.equal_self
#assert_no_axioms FX1Poly.Tier0.TwoCellCanonicity.equal_iff_canonicalForm
#assert_no_axioms FX1Poly.Tier0.strictTwoCellCanonicity
#assert_no_axioms FX1Poly.Tier0.strictTwoCellCanonicity_canonicalForm_id
#assert_no_axioms FX1Poly.Tier0.strictTwoCellNormalForm_exhaustive
#assert_no_axioms FX1Poly.Tier0.strictTwoCellCanonicity_discriminates
#assert_no_axioms FX1Poly.Tier0.strictTwoCellCanonicity_equal_iff_eq

-- Bundling the weak-Gray scaffolding + 2-cell canonicity INTO the ModeOmega capstone (the marker flips)
#assert_no_axioms FX1Poly.Tier0.ModeOmega.grayCategory
#assert_no_axioms FX1Poly.Tier0.ModeOmega.grayCategory_twoCategory
#assert_no_axioms FX1Poly.Tier0.ModeOmega.contractibleGlobularSkeleton
#assert_no_axioms FX1Poly.Tier0.ModeOmega.semistrictSignature
#assert_no_axioms FX1Poly.Tier0.ModeOmega.twoCellCanonicity
#assert_no_axioms FX1Poly.Tier0.ModeOmega.twoCell_equal_iff_canonicalForm

end FX1PolyAudit
