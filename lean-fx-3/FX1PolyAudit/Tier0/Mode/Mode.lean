import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Mode

/-! # FX1PolyAudit/AuditTier0ModePolygraph — zero-axiom gate for mode-0's mode polygraph data model

Per-declaration zero-axiom gate for `mode-0`'s design-lock deliverable (`FX1Poly/Tier0/Mode/Mode.lean`): the
MODE axis's polygraph data model — the 0/1-cell quiver (`ModeGraph`), the free 1-cells (`ModalityPath` + `length`
+ `identityPath` + `composePath` + the definitional left-identity smoke), the 2-polygraph signature
(`ModeSignature` with generating 2-cells between parallel paths), the FX mode-axis datum (`ModeAxisData` /
`fxModeAxis`), the degenerate base (`trivialModeSignature`), and the canonical NON-DEGENERATE witness — the
two-mode adjunction / cohesion seed (`AdjunctionMode` / `AdjunctionModality` / `adjunctionGraph` /
`adjunctionLeftThenRight` / `adjunctionRightThenLeft` / `AdjunctionTwoCell` / `adjunctionModeSignature`) with its
non-degeneracy witnesses.  The free strict 2-category + laws, decidable 2-cell equality, the weak ω-structure,
and the mode fibration are the honest deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The 0/1-cell quiver + the free 1-cells
#assert_no_axioms FX1Poly.Tier0.ModeGraph
#assert_no_axioms FX1Poly.Tier0.ModalityPath
#assert_no_axioms FX1Poly.Tier0.ModalityPath.length
#assert_no_axioms FX1Poly.Tier0.identityPath
#assert_no_axioms FX1Poly.Tier0.composePath
#assert_no_axioms FX1Poly.Tier0.composePath_identityPath_left

-- The 2-polygraph signature + the axis datum
#assert_no_axioms FX1Poly.Tier0.ModeSignature
#assert_no_axioms FX1Poly.Tier0.ModeAxisData

-- The degenerate base
#assert_no_axioms FX1Poly.Tier0.trivialModeGraph
#assert_no_axioms FX1Poly.Tier0.trivialModeSignature
#assert_no_axioms FX1Poly.Tier0.trivialModeSignature_modality_isEmpty

-- The canonical non-degenerate witness: the two-mode adjunction / cohesion seed
#assert_no_axioms FX1Poly.Tier0.AdjunctionMode
#assert_no_axioms FX1Poly.Tier0.AdjunctionModality
#assert_no_axioms FX1Poly.Tier0.adjunctionGraph
#assert_no_axioms FX1Poly.Tier0.adjunctionLeftThenRight
#assert_no_axioms FX1Poly.Tier0.adjunctionRightThenLeft
#assert_no_axioms FX1Poly.Tier0.AdjunctionTwoCell
#assert_no_axioms FX1Poly.Tier0.adjunctionModeSignature
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
