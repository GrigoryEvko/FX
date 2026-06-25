import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Step.StepRenameReflect

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.StepRenameReflect

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Reduction.Step.StepRenameReflect`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Pull a full `Step` (not just weak-head) back along an injective renaming: the confinement-free half of
-- full rename-reflection-with-image.  The left-inverse property holds at every index, so the round-trip
-- rename-inverse-after-rename = id collapses definitionally; Step.rename (forward) transports the step.
#assert_no_axioms FX1Poly.Core.Step.renamePullbackOfLeftInverse

#assert_no_axioms FX1Poly.Core.Step.renameReflectsExistsOfLeftInverse

#assert_no_axioms FX1Poly.Core.StepStar.renamePullbackOfLeftInverse

-- Generic head-recovery for a renamed cell (RawTerm.rename_eq_mkGen): rename rho term = mkGen gen _ _ implies
-- term = mkGen gen _ _.  The generator-generic head-recovery half of rename_eq_app/lam; the uniform first step
-- of every arm of full arbitrary-renaming Step reflection, a per-eliminator induction (the injective
-- renamePullback above does not serve the all-renamings Kripke-arrow CR3 closure).
#assert_no_axioms FX1Poly.Core.RawTerm.rename_eq_mkGen

end FX1PolyAudit
