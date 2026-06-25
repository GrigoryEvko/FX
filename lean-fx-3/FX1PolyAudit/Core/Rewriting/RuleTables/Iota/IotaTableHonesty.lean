import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableHonesty

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Iota.IotaTableHonesty

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableHonesty`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.iotaRuleDescOfOver

#assert_no_axioms FX1Poly.Core.iotaRuleDescOf

#assert_no_axioms FX1Poly.Core.iotaRuleDescOfOver_someInversion

#assert_no_axioms FX1Poly.Core.iotaRuleDescOfOver_complete

#assert_no_axioms FX1Poly.Core.Generator.hasReductionRule

#assert_no_axioms FX1Poly.Core.Generator.hasReductionRule_iff_existsRow

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

#assert_no_axioms FX1Poly.Core.hasReductionRule_var

#assert_no_axioms FX1Poly.Core.hasReductionRule_lam

#assert_no_axioms FX1Poly.Core.hasReductionRule_pathLam

#assert_no_axioms FX1Poly.Core.hasReductionRule_pair

#assert_no_axioms FX1Poly.Core.hasReductionRule_unit

#assert_no_axioms FX1Poly.Core.hasReductionRule_universeCode

#assert_no_axioms FX1Poly.Core.hasReductionRule_fixedPoint

#assert_no_axioms FX1Poly.Core.fireTableRedexOver_someInversion

#assert_no_axioms FX1Poly.Core.IotaRuleDesc.fireAtRoot?_pinsElimHead

#assert_no_axioms FX1Poly.Core.hasReductionRule_false_blocksRootFiring

#assert_no_axioms FX1Poly.Core.hasReductionRule_quotRec

#assert_no_axioms FX1Poly.Core.hasReductionRule_quotElim

#assert_no_axioms FX1Poly.Core.hasReductionRule_truncRec

end FX1PolyAudit
