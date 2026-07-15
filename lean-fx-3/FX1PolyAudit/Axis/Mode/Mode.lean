import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Mode

/-! # FX1PolyAudit/AuditAxisModePolygraph — zero-axiom gate for mode-0's FX mode-axis datum

Per-declaration zero-axiom gate for `mode-0`'s design-lock deliverable (`FX1Poly/Axis/Mode/Mode.lean`): the
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
#assert_no_axioms FX1Poly.Axis.ModeAxisData

-- The degenerate base
#assert_no_axioms FX1Poly.Axis.trivialModeGraph
#assert_no_axioms FX1Poly.Axis.trivialModeSignature
#assert_no_axioms FX1Poly.Axis.trivialModeSignature_modality_isEmpty

-- The FX mode-axis datum carries the non-degenerate adjunction seed
#assert_no_axioms FX1Poly.Axis.fxModeAxis

-- Non-degeneracy witnesses + the fx pin
#assert_no_axioms FX1Poly.Axis.adjunctionHasTwoDistinctModes
#assert_no_axioms FX1Poly.Axis.adjunctionHasDirectedModality
#assert_no_axioms FX1Poly.Axis.adjunctionUnitBoundariesDistinct
#assert_no_axioms FX1Poly.Axis.fxModeAxis_signature_isAdjunction

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasStrictTwoCategoryCore
#assert_no_axioms FX1Poly.Axis.fxMode_hasDecidableTwoCellEquality
#assert_no_axioms FX1Poly.Axis.fxMode_hasDecidableFreeTwoCellEquality
#assert_no_axioms FX1Poly.Axis.fxMode_hasWeakOmegaStructure
#assert_no_axioms FX1Poly.Axis.fxMode_hasModeFibration

end FX1PolyAudit
