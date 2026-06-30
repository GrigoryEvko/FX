import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.TwoCategoryCore

/-! # FX1PolyAudit/AuditTier0ModeTwoCategoryCore — zero-axiom gate for mode-1's free-category core

Per-declaration zero-axiom gate for `mode-1`'s mode-axis deliverable (`FX1Poly/Tier0/Mode/TwoCategoryCore.lean`):
the path-category laws (`composePath_assoc`, `composePath_identityPath_right`), the free 1-category on a mode
quiver as a `RawCategory` (`freeModeCategory`, the shared-substrate connection) with its 1-cell round-trip and the
generator embedding (`singletonModalityPath`), the free 2-category on a mode quiver (`freeModeTwoCategory`) and its
base round-trip, decidable 1-cell equality (`modalityPathDecEq`), the §3.13 `ModeTheory` / `RigidModeTheory` round
trips, plus the honesty markers.  The GENERIC strict-2-category core it builds on (`RawTwoCategory`,
`locallyDiscreteTwoCategory`, `IsRigid`, `rigidTwoCellDecEq`, `locallyDiscreteTwoCategory_isRigid`) is gated in
`FX1PolyAudit.Polygraph.TwoCategory.TwoCategoryCore`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The free 1-category on the mode quiver
#assert_no_axioms FX1Poly.Tier0.composePath_assoc
#assert_no_axioms FX1Poly.Tier0.composePath_identityPath_right
#assert_no_axioms FX1Poly.Tier0.freeModeCategory
#assert_no_axioms FX1Poly.Tier0.freeModeCategory_morphism_eq_modalityPath
#assert_no_axioms FX1Poly.Tier0.singletonModalityPath
#assert_no_axioms FX1Poly.Tier0.singletonModalityPath_length

-- The free 2-category on the mode quiver
#assert_no_axioms FX1Poly.Tier0.freeModeTwoCategory
#assert_no_axioms FX1Poly.Tier0.freeModeTwoCategory_base

-- Faithfulness + decidable 1-cell equality (§3.13 oneCellEqDecidable) + the free mode theory
#assert_no_axioms FX1Poly.Tier0.singletonModalityPath_injective
#assert_no_axioms FX1Poly.Tier0.ModalityPath.firstStepTarget
#assert_no_axioms FX1Poly.Tier0.modalityPathDecEq
#assert_no_axioms FX1Poly.Tier0.ModeTheory
#assert_no_axioms FX1Poly.Tier0.freeModeTheory
#assert_no_axioms FX1Poly.Tier0.freeModeTheory_twoCategory

-- The rigid / SProp mode theory (§3.13)
#assert_no_axioms FX1Poly.Tier0.freeModeTwoCategory_isRigid
#assert_no_axioms FX1Poly.Tier0.RigidModeTheory
#assert_no_axioms FX1Poly.Tier0.freeRigidModeTheory

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasFreeTwoCellGeneratorModel
#assert_no_axioms FX1Poly.Tier0.fxMode_hasModeTheoryStructureClass

end FX1PolyAudit
