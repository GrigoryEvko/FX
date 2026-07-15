import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.ModalInduction

/-! # FX1PolyAudit/AuditAxisModeModalInduction — zero-axiom gate for mode-10

Per-declaration zero-axiom gate for `mode-10` (`FX1Poly/Axis/Mode/ModalInduction.lean`): the modal eliminator
+ its β-coherence + the identity witness + the derived `mapModal` / `mapModal_intro`, the crisp-J principle + its
β + the `Eq.rec` witness + the derived `transport` / `transport_refl`, the mode tie, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The modal eliminator + its coherence + the derived functoriality
#assert_no_axioms FX1Poly.Axis.ModalEliminator
#assert_no_axioms FX1Poly.Axis.identityModalEliminator
#assert_no_axioms FX1Poly.Axis.ModalEliminator.mapModal
#assert_no_axioms FX1Poly.Axis.ModalEliminator.mapModal_intro
#assert_no_axioms FX1Poly.Axis.identityModalEliminator_modalType

-- Crisp-J + its β + the witness + the derived transport
#assert_no_axioms FX1Poly.Axis.CrispJ
#assert_no_axioms FX1Poly.Axis.equalityCrispJ
#assert_no_axioms FX1Poly.Axis.CrispJ.transport
#assert_no_axioms FX1Poly.Axis.CrispJ.transport_refl

-- The mode-indexed modal eliminator (indexed by the mode-1 1-cells)
#assert_no_axioms FX1Poly.Axis.ModeIndexedModalEliminator
#assert_no_axioms FX1Poly.Axis.identityModeIndexedModalEliminator
#assert_no_axioms FX1Poly.Axis.ModeIndexedModalEliminator.mapModal
#assert_no_axioms FX1Poly.Axis.ModeIndexedModalEliminator.mapModal_intro
#assert_no_axioms FX1Poly.Axis.ModeIndexedModalEliminator.subsumeEq
#assert_no_axioms FX1Poly.Axis.ModeIndexedModalEliminator.subsumeEq_rfl
#assert_no_axioms FX1Poly.Axis.identityModeIndexedModalEliminator_modalType

-- Honesty markers
#assert_no_axioms FX1Poly.Axis.fxMode_hasModeIndexedModalEliminator
#assert_no_axioms FX1Poly.Axis.fxMode_hasKernelModalSyntaxConnection
#assert_no_axioms FX1Poly.Axis.fxMode_hasRealCohesiveCrispJ

end FX1PolyAudit
