import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.DataElimUnionSpike

/-! # FX1PolyAudit/AuditNativeWaveDataElim — zero-axiom gate for the NATIVE-28 non-recursive
    data-eliminator rows on the seed union (`DataElimUnionSpike` + adequacy + typed ι smokes + verdict).

Per-declaration `#assert_no_axioms` gate: each shipped declaration's axiom closure is verified empty
(no `propext` / `Quot.sound` / `Classical.choice` / `sorry` / `native_decide` / `omega`).  This is the
command-time fail-fast gate; it INSPECTS the axiom closure of the kernel theorems and fails the build if
any is non-empty. -/

namespace FX1PolyAudit

open FX1Poly.Typed

/-! ## Shape-1 table (two-branch match: boolElim / optionMatch / eitherMatch) -/

#assert_no_axioms FX1Poly.Typed.boolElimMatchRule
#assert_no_axioms FX1Poly.Typed.optionMatchMatchRule
#assert_no_axioms FX1Poly.Typed.eitherMatchMatchRule
#assert_no_axioms FX1Poly.Typed.twoBranchMatchRuleOf
#assert_no_axioms FX1Poly.Typed.twoBranchMatchRuleOf_boolElim
#assert_no_axioms FX1Poly.Typed.twoBranchMatchRuleOf_optionMatch
#assert_no_axioms FX1Poly.Typed.twoBranchMatchRuleOf_eitherMatch

/-! ## Shape-2 table (path induction: idJ) -/

#assert_no_axioms FX1Poly.Typed.idJPathInductionRule
#assert_no_axioms FX1Poly.Typed.pathInductionRuleOf
#assert_no_axioms FX1Poly.Typed.pathInductionRuleOf_idJ

/-! ## Shape-3 table (projection: fst / snd) -/

#assert_no_axioms FX1Poly.Typed.fstProjectionRule
#assert_no_axioms FX1Poly.Typed.sndProjectionRule
#assert_no_axioms FX1Poly.Typed.projectionRuleOf
#assert_no_axioms FX1Poly.Typed.projectionRuleOf_fst
#assert_no_axioms FX1Poly.Typed.projectionRuleOf_snd

/-! ## The spike judgment -/

#assert_no_axioms FX1Poly.Typed.DataElimUnionSpike

/-! ## Adequacy (premise parity): every bespoke derivation maps into the spike -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescBoolElim.toDataElimUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescOptionMatch.toDataElimUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescEitherMatch.toDataElimUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescIdElim.toDataElimUnionSpike
#assert_no_axioms FX1Poly.Typed.HasTypeDescSigmaProjection.toDataElimUnionSpike

/-! ## Typed ι smokes: the eliminator fires and the reduct types in the spike -/

#assert_no_axioms FX1Poly.Typed.DataElimUnionSpike.ofGrownTyping
#assert_no_axioms FX1Poly.Typed.boolElimTrueIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.boolElimFalseIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.optionMatchNoneIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.optionMatchSomeIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.eitherMatchInlIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.eitherMatchInrIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.idJReflIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.fstProjectionIotaSpikeTyped
#assert_no_axioms FX1Poly.Typed.sndProjectionIotaSpikeTyped

/-! ## The coverage / verdict gate -/

#assert_no_axioms FX1Poly.Typed.DataElimRowCoverage
#assert_no_axioms FX1Poly.Typed.dataElimRowCoverageWitness

end FX1PolyAudit
