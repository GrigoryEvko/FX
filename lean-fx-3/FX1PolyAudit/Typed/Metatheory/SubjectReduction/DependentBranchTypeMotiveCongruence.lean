import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.DependentBranchTypeMotiveCongruence

/-! # FX1PolyAudit/DependentBranchTypeMotiveCongruence — dependent-branch-type motive-congruence audit shard

Per-declaration zero-axiom gate for the five dependent-branch-type `Conv`-stability lemmas under a motive step
(gate-2 motive-step substrate, TYTAB-2-FT-SR #1697): natElim/natRec succ, optionMatch some, eitherMatch
inl/inr, listElim cons. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.natElimDependentSuccBranchType_isConvStableUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.optionMatchDependentSomeBranchType_isConvStableUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInlBranchType_isConvStableUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInrBranchType_isConvStableUnderMotiveStep
#assert_no_axioms FX1Poly.Typed.listElimDependentConsBranchType_isConvStableUnderMotiveStep

end FX1PolyAudit
