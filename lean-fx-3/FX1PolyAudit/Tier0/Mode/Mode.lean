import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Mode

/-! # FX1PolyAudit/AuditTier0ModePolygraph — zero-axiom gate for mode-0's FX mode-axis datum

Per-declaration zero-axiom gate for `mode-0`'s design-lock deliverable (`FX1Poly/Tier0/Mode/Mode.lean`): the
MODE axis's choices over the generic computad carrier — the FX mode-axis datum (`ModeAxisData` / `fxModeAxis`),
the degenerate base (`trivialModeGraph` / `trivialModeSignature`), and the non-degeneracy witnesses pinning the
adjunction seed as `fxModeAxis`'s signature.  The GENERIC carrier it imports — the quiver, the free 1-cells and
their laws, decidable equality, `ModeSignature`, and the adjunction seed — is gated in
`FX1PolyAudit.Polygraph.Computad.Signature` / `FX1PolyAudit.Polygraph.Computad.AdjunctionSeed`.  The free strict
2-category + laws, decidable 2-cell equality, and the weak ω-structure are the honest deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The FX mode-axis datum
#assert_no_axioms FX1Poly.Tier0.ModeAxisData

-- The degenerate base
#assert_no_axioms FX1Poly.Tier0.trivialModeGraph
#assert_no_axioms FX1Poly.Tier0.trivialModeSignature
#assert_no_axioms FX1Poly.Tier0.trivialModeSignature_modality_isEmpty

-- The FX mode-axis datum carries the non-degenerate adjunction seed
#assert_no_axioms FX1Poly.Tier0.fxModeAxis

-- Non-degeneracy witnesses + the fx pin
#assert_no_axioms FX1Poly.Tier0.adjunctionHasTwoDistinctModes
#assert_no_axioms FX1Poly.Tier0.adjunctionHasDirectedModality
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitBoundariesDistinct
#assert_no_axioms FX1Poly.Tier0.fxModeAxis_signature_isAdjunction

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasStrictTwoCategoryCore
#assert_no_axioms FX1Poly.Tier0.fxMode_hasDecidableTwoCellEquality
#assert_no_axioms FX1Poly.Tier0.fxMode_hasWeakOmegaStructure
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeFibration

end FX1PolyAudit
