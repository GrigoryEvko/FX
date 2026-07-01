import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Computad.Signature

/-! # FX1PolyAudit.Polygraph.Computad.Signature — zero-axiom gate for the generic 2-computad carrier

Per-declaration zero-axiom gate for the signature-free computad carrier (`FX1Poly/Polygraph/Computad/Signature.lean`):
the 0/1-cell quiver (`ModeGraph`), the free 1-cells (`ModalityPath` + `length` + `identityPath` + `composePath`
with the three category laws), the generator embedding (`singletonModalityPath` + faithfulness), decidable
1-cell equality (`ModalityPath.firstStepTarget` / `modalityPathDecEq`), and the 2-polygraph signature
(`ModeSignature`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The 0/1-cell quiver + the free 1-cells with their category laws
#assert_no_axioms FX1Poly.Tier0.ModeGraph
#assert_no_axioms FX1Poly.Tier0.ModalityPath
#assert_no_axioms FX1Poly.Tier0.ModalityPath.length
#assert_no_axioms FX1Poly.Tier0.identityPath
#assert_no_axioms FX1Poly.Tier0.composePath
#assert_no_axioms FX1Poly.Tier0.composePath_identityPath_left
#assert_no_axioms FX1Poly.Tier0.composePath_assoc
#assert_no_axioms FX1Poly.Tier0.composePath_identityPath_right

-- The generator embedding + its faithfulness
#assert_no_axioms FX1Poly.Tier0.singletonModalityPath
#assert_no_axioms FX1Poly.Tier0.singletonModalityPath_length
#assert_no_axioms FX1Poly.Tier0.singletonModalityPath_injective

-- Decidable equality of 1-cells (§3.13 oneCellEqDecidable)
#assert_no_axioms FX1Poly.Tier0.ModalityPath.firstStepTarget
#assert_no_axioms FX1Poly.Tier0.modalityPathDecEq

-- The 2-polygraph signature
#assert_no_axioms FX1Poly.Tier0.ModeSignature

end FX1PolyAudit
