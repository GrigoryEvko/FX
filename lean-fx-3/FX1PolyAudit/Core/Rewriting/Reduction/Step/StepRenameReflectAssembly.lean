import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Reduction.Step.StepRenameReflectAssembly

/-! # FX1PolyAudit.Core.Rewriting.Reduction.Step.StepRenameReflectAssembly

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Reduction.Step.StepRenameReflectAssembly`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- THE FULL ASSEMBLY (StepRenameReflectAssembly.lean): the complete arbitrary-renaming Step
-- reflection-with-image Step (rename rho t) u → ∃ t', Step t t' ∧ rename rho t' = u — TABLE-ROUTED:
-- the generic StepOverTable.reflectRename (two arms: root firing via firesOn?_rename, congruence
-- recursion) at the 17-row legacy table, transported across the IOTA-T1 adequacy
-- stepOverTable_iff_step. The bespoke 18-arm dispatch is retired. This is the
-- Kripke-arrow-CR3 ingredient the open-context (Kripke) logical relation needs to discharge
-- GrownCtxConv-5, the grown context-conversion piElim crux.
#assert_no_axioms FX1Poly.Core.Step.reflectRename

-- Reflection corollary replacing the historical 950-line per-constructor freshness
-- induction: a reduct of a weakened term strengthens to its singleton-substitution form.
#assert_no_axioms FX1Poly.Core.Step.weaken_strengthenTarget

end FX1PolyAudit
