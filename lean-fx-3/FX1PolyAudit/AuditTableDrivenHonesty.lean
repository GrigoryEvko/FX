import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.TypedByTableUnion
import FX1Poly.Typed.TableTypingUnionDivergence

/-! # FX1PolyAudit/AuditTableDrivenHonesty — the honesty-classifier collapse audit shard

Per-declaration zero-axiom gate for the table-driven honesty-classifier collapse: the table-driven classifier
`hasTableTypingRule` (the data-family decides folded into native-table membership), the exact equivalence to
`hasSomeTypingRule` (the delete-readiness evidence), the per-family LIVE witnesses, the table-driven false-peel
and its named per-table projections (the per-table positional-peel replacement), the per-table introduction
lemmas, the grown bridge re-derived from the table peel, the soundness bundle rebased onto the table classifier,
the four-decide irreducible-residual characterization, and the union-divergence findings (the four heads the
union types yet the honesty classifier brands reserved).  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## ★ Leg B — the exact equivalence -/

#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_eq_hasTableTypingRule

/-! ## Leg A — per-family LIVE witnesses -/

#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_boolElim
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_optionMatch
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_eitherMatch
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_idJ
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_fst
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_snd
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_natSucc
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_listCons
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_optionSome
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_optionNone
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_eitherInl
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_eitherInr
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_pair
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_refl
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_pathLam
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_pathApp

/-! ## ★ Leg C / NATIVE-41 — the table-driven false-peel + per-table projections -/

#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_falsePeel
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_typingRuleDescOf_false
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_introRuleDescOf_false
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_elimRuleDescOf_false
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_nativeTwoBranchMatch_false
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_nativePathInduction_false
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_nativeProjection_false

/-! ## NATIVE-41 — per-table introduction lemmas -/

#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_of_nativeTwoBranchMatch
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_of_nativePathInduction
#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_of_nativeProjection

/-! ## ★ Leg C — the grown bridge re-derived from the table peel + the soundness bundle -/

#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_false_imp_isUntypableHead
#assert_no_axioms FX1Poly.Typed.reservedTableHeadUntypedByEveryEngine

/-! ## The irreducible four-decide residual -/

#assert_no_axioms FX1Poly.Typed.tableClassifierResidualHeadsLive
#assert_no_axioms FX1Poly.Typed.natZeroNativeIntroTableResidency

/-! ## The union-divergence findings (the honesty ledger is stale vs the union) -/

#assert_no_axioms FX1Poly.Typed.hasTableTypingRule_le_hasUnionEliminatorTypingRule
#assert_no_axioms FX1Poly.Typed.idCodeUnionTypableButHonestyReserved
#assert_no_axioms FX1Poly.Typed.natElimUnionTypableButHonestyReserved
#assert_no_axioms FX1Poly.Typed.natRecUnionTypableButHonestyReserved
#assert_no_axioms FX1Poly.Typed.listElimUnionTypableButHonestyReserved
#assert_no_axioms FX1Poly.Typed.unionEliminatorClassifierStrictlyExtendsHonestyClassifier

end FX1PolyAudit
