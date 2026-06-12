import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.IotaTableHonesty

/-! # FX1PolyAudit/AuditIotaTableHonesty — IOTA-T9 honesty-seam shard

Per-declaration zero-axiom gate for the table-derived reduction-rule
honesty: the row lookup with inversion/completeness, the
`hasReductionRule` classifier with its existential characterization,
the per-head pins (including the deliberate `gen_fixedPoint` omission),
and the root-firing honesty.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

/-! ## The row lookup -/

#assert_no_axioms FX1Poly.Core.iotaRuleDescOfOver
#assert_no_axioms FX1Poly.Core.iotaRuleDescOf
#assert_no_axioms FX1Poly.Core.iotaRuleDescOfOver_someInversion
#assert_no_axioms FX1Poly.Core.iotaRuleDescOfOver_complete

/-! ## The honesty classifier -/

#assert_no_axioms FX1Poly.Core.Generator.hasReductionRule
#assert_no_axioms FX1Poly.Core.Generator.hasReductionRule_iff_existsRow

/-! ## Per-head pins — eliminators -/

#assert_no_axioms FX1Poly.Core.hasReductionRule_app
#assert_no_axioms FX1Poly.Core.hasReductionRule_pathApp
#assert_no_axioms FX1Poly.Core.hasReductionRule_boolElim
#assert_no_axioms FX1Poly.Core.hasReductionRule_fst
#assert_no_axioms FX1Poly.Core.hasReductionRule_snd
#assert_no_axioms FX1Poly.Core.hasReductionRule_natElim
#assert_no_axioms FX1Poly.Core.hasReductionRule_natRec
#assert_no_axioms FX1Poly.Core.hasReductionRule_listElim
#assert_no_axioms FX1Poly.Core.hasReductionRule_optionMatch
#assert_no_axioms FX1Poly.Core.hasReductionRule_eitherMatch
#assert_no_axioms FX1Poly.Core.hasReductionRule_idJ
#assert_no_axioms FX1Poly.Core.hasReductionRule_idStrictRec

/-! ## Per-head pins — rule-free heads + the fixedPoint omission -/

#assert_no_axioms FX1Poly.Core.hasReductionRule_var
#assert_no_axioms FX1Poly.Core.hasReductionRule_lam
#assert_no_axioms FX1Poly.Core.hasReductionRule_pathLam
#assert_no_axioms FX1Poly.Core.hasReductionRule_pair
#assert_no_axioms FX1Poly.Core.hasReductionRule_unit
#assert_no_axioms FX1Poly.Core.hasReductionRule_universeCode
#assert_no_axioms FX1Poly.Core.hasReductionRule_fixedPoint

/-! ## Root-firing honesty -/

#assert_no_axioms FX1Poly.Core.fireTableRedexOver_someInversion
#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_pinsElimHead
#assert_no_axioms FX1Poly.Core.hasReductionRule_false_blocksRootFiring

end FX1PolyAudit
