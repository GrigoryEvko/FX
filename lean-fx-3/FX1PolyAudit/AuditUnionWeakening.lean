import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.HasTypeUnionWeakening

/-! # FX1PolyAudit/AuditUnionWeakening — audit shard for the RENAMING / WEAKENING lemma over the
    25-arm native union (the de-Bruijn-insertion twin of `HasTypeUnion.substRespectingContext`)

Per-declaration zero-axiom gate for the union weakening primitive: the per-cell renaming commutations
(the rename twins of `subst_*Cell`), the lift/weaken naturality squares, the composite-arrow renaming
commutations, the eight data-engine rename twins (the rename mirror of `NativeUnionEngineSubstitution`),
the affine-binder-check transport, the renaming-respects-context carrier / two-binder helper, the
pointwise renaming lemma over the union (`renameRespectingContext`, all 25 arms), and the weakening
corollary (`weakenUnderBinding`).  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Per-cell renaming commutations (the rename twins of the `subst_*Cell` lemmas) -/

#assert_no_axioms FX1Poly.Typed.rename_natTypeCell
#assert_no_axioms FX1Poly.Typed.rename_natSuccCell
#assert_no_axioms FX1Poly.Typed.rename_listConsCell
#assert_no_axioms FX1Poly.Typed.rename_optionSomeCell
#assert_no_axioms FX1Poly.Typed.rename_optionNoneCell
#assert_no_axioms FX1Poly.Typed.rename_eitherInlCell
#assert_no_axioms FX1Poly.Typed.rename_eitherInrCell
#assert_no_axioms FX1Poly.Typed.rename_pairCell
#assert_no_axioms FX1Poly.Typed.rename_reflCell
#assert_no_axioms FX1Poly.Typed.rename_listTypeCell
#assert_no_axioms FX1Poly.Typed.rename_optionTypeCell
#assert_no_axioms FX1Poly.Typed.rename_eitherTypeCell
#assert_no_axioms FX1Poly.Typed.rename_productTypeCell
#assert_no_axioms FX1Poly.Typed.rename_idTypeCell
#assert_no_axioms FX1Poly.Typed.rename_bridgeTypeCell
#assert_no_axioms FX1Poly.Typed.rename_natElimCell
#assert_no_axioms FX1Poly.Typed.rename_natRecCell
#assert_no_axioms FX1Poly.Typed.rename_boolElimCell
#assert_no_axioms FX1Poly.Typed.rename_optionMatchCell
#assert_no_axioms FX1Poly.Typed.rename_eitherMatchCell
#assert_no_axioms FX1Poly.Typed.rename_idJCell
#assert_no_axioms FX1Poly.Typed.rename_fstCell
#assert_no_axioms FX1Poly.Typed.rename_sndCell
#assert_no_axioms FX1Poly.Typed.rename_listElimCell
#assert_no_axioms FX1Poly.Typed.rename_pathLamCell
#assert_no_axioms FX1Poly.Typed.rename_pathAppCell

/-! ## Lift/weaken naturality squares + composite-arrow renaming commutations -/

#assert_no_axioms FX1Poly.Typed.rename_iterateLift_one_renameWeaken_commute
#assert_no_axioms FX1Poly.Typed.rename_iterateLift_one_weaken_commute
#assert_no_axioms FX1Poly.Typed.rename_iterateLift_two_weaken_weaken_commute
#assert_no_axioms FX1Poly.Typed.rename_nonDependentArrow
#assert_no_axioms FX1Poly.Typed.rename_listStepFunctionType

/-! ## Per-table rename stability (the table-driven-arm legs) -/

#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_outputRenameStable
#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_outputRenameStable
#assert_no_axioms FX1Poly.Typed.FlatDescTelescopePi.renameRespectingTelescope

/-! ## The renaming-respects-context carrier + binder helpers + affine-binder-check transport -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.RenameRespectsContext
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.RenameRespectsContext.consTwice
#assert_no_axioms FX1Poly.Typed.gradedBinderChecks_rename_lift

/-! ## ★ The pointwise renaming lemma over the union (all 25 arms) + the weakening corollary -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.renameRespectingContext
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.weakenUnderBinding

end FX1PolyAudit
