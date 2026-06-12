import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.EtaRuleTable

/-! # FX1PolyAudit/AuditEtaRuleTable — ETA-T0 audit shard

Per-declaration zero-axiom gate for the eta-rule schema: the
`strengthenBy?` un-weakening engine with its roundtrip pins, the
shift-checked child lookup, the observation schema and contraction
engine, the five rows with the slot ground-truth pins, the tier ledger,
and the concrete contraction pins (including the non-left-linearity
NEGATIVE).  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The un-weakening engine -/

#assert_no_axioms FX1Poly.Core.RawTerm.strengthenBy?
#assert_no_axioms FX1Poly.Core.RawTerm.strengthenBy?_weakenBy
#assert_no_axioms FX1Poly.Core.RawTerm.weakenBy_strengthenBy?

/-! ## The lookup + observation schema -/

#assert_no_axioms FX1Poly.Core.RawTermChildren.childAtShift?
#assert_no_axioms FX1Poly.Core.EtaObservationSpec
#assert_no_axioms FX1Poly.Core.observerFreshVarsHold
#assert_no_axioms FX1Poly.Core.EtaObservationSpec.extractCoreFrom?

/-! ## The rule descriptor + contraction engine -/

#assert_no_axioms FX1Poly.Core.EtaRuleDesc
#assert_no_axioms FX1Poly.Core.etaObservationsAgree
#assert_no_axioms FX1Poly.Core.EtaRuleDesc.contractsOn?

/-! ## Slot ground truth -/

#assert_no_axioms FX1Poly.Core.gen_lam_binderShifts
#assert_no_axioms FX1Poly.Core.gen_pair_binderShifts
#assert_no_axioms FX1Poly.Core.gen_pathLam_binderShifts
#assert_no_axioms FX1Poly.Core.gen_modIntro_binderShifts
#assert_no_axioms FX1Poly.Core.gen_glueIntro_binderShifts

/-! ## The five rows + the table -/

#assert_no_axioms FX1Poly.Core.etaLamRow
#assert_no_axioms FX1Poly.Core.etaPairRow
#assert_no_axioms FX1Poly.Core.etaPathLamRow
#assert_no_axioms FX1Poly.Core.etaModIntroRow
#assert_no_axioms FX1Poly.Core.etaGlueIntroRow
#assert_no_axioms FX1Poly.Core.etaRuleTable
#assert_no_axioms FX1Poly.Core.etaRuleTable_length
#assert_no_axioms FX1Poly.Core.etaRuleTable_typedTierLedger

/-! ## The GO gate — concrete contraction pins -/

#assert_no_axioms FX1Poly.Core.etaLamRow_contractsOnConcrete
#assert_no_axioms FX1Poly.Core.etaLamRow_rejectsNonVarArgument
#assert_no_axioms FX1Poly.Core.etaPairRow_contractsOnConcrete
#assert_no_axioms FX1Poly.Core.etaPairRow_rejectsDisagreeingCores
#assert_no_axioms FX1Poly.Core.etaPathLamRow_contractsOnConcrete
#assert_no_axioms FX1Poly.Core.etaModIntroRow_contractsOnConcrete
#assert_no_axioms FX1Poly.Core.etaGlueIntroRow_contractsOnConcrete

end FX1PolyAudit
