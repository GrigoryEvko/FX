import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionUnionSubstituent
import FX1Poly.Typed.Cell.NatElimDependentSuccType
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.ListElimDependentConsType

/-! # FX1PolyAudit/AuditUnionSubstitution — NATIVE-37 part b audit shard (the SUBSTITUTION lemma for
    the 24-arm native union + the 2-variable corollaries + the general succ-branch ι discharge)

Per-declaration zero-axiom gate for NATIVE-37 part b: the occurrence-under-lifted-subst master lemma (the
graded-arm prerequisite), the per-cell substitution commutations, the per-engine substitution lemmas (the
embedding-arm legs), the pointwise substitution lemma over the union (`substRespectingContext`, all 24
arms), the affine-binder-check transport, the two-variable corollaries (`substPairUnderTwoBindings` /
`substPairNonDependent`), the recursive-call construction (`natElimRecursiveCallUnionTyped` /
`natRecRecursiveCallUnionTyped` — the recursion loop closed through the union's recursiveElim arm), the
general succ-branch ι discharges (`natElimSuccIotaComputesTypedInUnion` /
`natRecSuccIotaComputesTypedInUnion`), and the coverage record / witness.  Every declaration below must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The occurrence-under-lifted-subst master lemma (the graded-arm prerequisite) -/

#assert_no_axioms FX1Poly.Core.occurrenceCountAt_var_of_ne
#assert_no_axioms FX1Poly.Core.occurrenceCountAt_var_succ_eq
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_hitProfile_succ
#assert_no_axioms FX1Poly.Core.iterateLiftRaw_hitProfile_raised
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst_hitProfile
#assert_no_axioms FX1Poly.Core.RawTermChildren.occurrenceCountAt_subst_hitProfile
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_hitsExactlyAt_zero
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst_lift_zeroPosition

/-! ## Per-cell substitution commutations -/

#assert_no_axioms FX1Poly.Typed.subst_natTypeCell
#assert_no_axioms FX1Poly.Typed.subst_natSuccCell
#assert_no_axioms FX1Poly.Typed.subst_natElimCell
#assert_no_axioms FX1Poly.Typed.subst_natRecCell
#assert_no_axioms FX1Poly.Typed.subst_boolElimCell
#assert_no_axioms FX1Poly.Typed.subst_optionMatchCell
#assert_no_axioms FX1Poly.Typed.subst_eitherMatchCell
#assert_no_axioms FX1Poly.Typed.subst_idJCell
#assert_no_axioms FX1Poly.Typed.subst_fstCell
#assert_no_axioms FX1Poly.Typed.subst_sndCell
#assert_no_axioms FX1Poly.Typed.subst_listElimCell
#assert_no_axioms FX1Poly.Typed.subst_pathLamCell
#assert_no_axioms FX1Poly.Typed.subst_pathAppCell
#assert_no_axioms FX1Poly.Typed.subst_listStepFunctionType
#assert_no_axioms FX1Poly.Typed.subst_listElimDependentConsBranchType_iterateLift
#assert_no_axioms FX1Poly.Typed.subst_nonDependentArrow

/-! ## ★ The cons-branch APP-SPINE output-type reshapings (DEP-LIST sub-D2b) — the triple-application
    intermediate types + collapse lemmas the dependent cons-ι subject reduction rides. -/

#assert_no_axioms FX1Poly.Typed.listElimDependentConsTypeAfterHead
#assert_no_axioms FX1Poly.Typed.listElimDependentConsTypeAfterHeadTail
#assert_no_axioms FX1Poly.Typed.subst0_listElimConsBranchOuterCodomain_afterHead
#assert_no_axioms FX1Poly.Typed.subst0_subst_lift_singleton_listElimDependentRecBinderType
#assert_no_axioms FX1Poly.Typed.subst0_listElimConsTypeAfterHead_afterHeadTail
#assert_no_axioms FX1Poly.Typed.subst0_listElimConsTypeAfterHeadTailCodomain_consIota

/-! ## ★ The dependent two-binder succ-branch type + its succ-ι type-preservation pin (DEP-NAT-WIRE)

The recursor's succ branch is the FIRST genuinely two-binder dependent eliminator branch (bool's ctors are
nullary; option / either / nat-rule / list / id rules are all still NON-dependent).  Its classifier
`natElimDependentSuccBranchType` is the motive re-based at `natSucc (var 1)` with a `+2` weakening;
`subst_natElimDependentSuccBranchType_succIota` is the subject-reduction obligation — the succ-ι substitution
collapses the composite to `singleton (natSucc predecessor)`, carrying the branch type to
`subst0 motive (natSucc predecessor)`.  Both axiom-free via `subst_compose` + `subst_pointwise`. -/

#assert_no_axioms FX1Poly.Typed.natElimDependentSuccBranchType
#assert_no_axioms FX1Poly.Typed.subst_natElimDependentSuccBranchType_succIota
#assert_no_axioms FX1Poly.Typed.subst_natElimDependentSuccBranchType_general
#assert_no_axioms FX1Poly.Typed.subst_consSingleton_substLiftLift

/-! ## ★ The dependent ONE-binder coproduct branch codomains + their naturality laws (DEP-EITHER)

The dependent `eitherMatch` carries TWO single-binder branches `(a : A) → motive (inl a)` and
`(b : B) → motive (inr b)` — the FIRST one-binder dependent eliminator branches (between bool's nullary
ctors and nat's two-binder succ branch).  Each codomain re-bases the motive at `inl (var 0)` / `inr (var 0)`
with a `+1` weakening; the ι pins (`subst0 … = subst0 motive (inl/inr payload)`) are the subject-reduction
obligations for the injection-ι reducts, the `_general` forms are the FT-bridge under a closing substitution,
and the substitution/renaming-stability twins feed `substRespectingContext` / `renameRespectsContext`.  All
axiom-free via `subst_compose` + `subst_pointwise` + the renaming bridge (`weaken_eq_substShiftBy1`). -/

#assert_no_axioms FX1Poly.Typed.weaken_eq_substShiftBy1
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInlBranchCodomain
#assert_no_axioms FX1Poly.Typed.subst0_eitherMatchDependentInlBranchCodomain_inlIota
#assert_no_axioms FX1Poly.Typed.subst_eitherMatchDependentInlBranchCodomain_general
#assert_no_axioms FX1Poly.Typed.subst_eitherMatchDependentInlBranchCodomain_substLift
#assert_no_axioms FX1Poly.Typed.subst_eitherMatchDependentInlBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.rename_eitherMatchDependentInlBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInrBranchCodomain
#assert_no_axioms FX1Poly.Typed.subst0_eitherMatchDependentInrBranchCodomain_inrIota
#assert_no_axioms FX1Poly.Typed.subst_eitherMatchDependentInrBranchCodomain_general
#assert_no_axioms FX1Poly.Typed.subst_eitherMatchDependentInrBranchCodomain_substLift
#assert_no_axioms FX1Poly.Typed.subst_eitherMatchDependentInrBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.rename_eitherMatchDependentInrBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInlBranchType
#assert_no_axioms FX1Poly.Typed.eitherMatchDependentInrBranchType

/-! ## The dependent `optionMatch` `some`-branch codomain + type (DEP-OPTION brick 1).  Option is a `bool`/`either`
hybrid: the `none` branch is nullary (`subst0 motive optionNoneCell`, no ledger) and only the `some` branch is a
single-binder dependent function `(a : A) → motive (some a)`.  Same `subst_compose` + `subst_pointwise` + the
renaming bridge as the `eitherMatch` inl side. -/

#assert_no_axioms FX1Poly.Typed.optionMatchDependentSomeBranchCodomain
#assert_no_axioms FX1Poly.Typed.subst0_optionMatchDependentSomeBranchCodomain_someIota
#assert_no_axioms FX1Poly.Typed.subst_optionMatchDependentSomeBranchCodomain_general
#assert_no_axioms FX1Poly.Typed.subst_optionMatchDependentSomeBranchCodomain_substLift
#assert_no_axioms FX1Poly.Typed.subst_optionMatchDependentSomeBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.rename_optionMatchDependentSomeBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.optionMatchDependentSomeBranchType
#assert_no_axioms FX1Poly.Typed.subst_optionMatchDependentSomeBranchType_iterateLift
#assert_no_axioms FX1Poly.Typed.rename_optionMatchDependentSomeBranchType_iterateLift

/-! ## The dependent `listElim` `cons`-branch codomain + recursive-result binder type + wrapped type
(DEP-LIST sub-D1).  List's cons branch is the BINARY, recursive generalization of `eitherMatch`'s injection
branches: a THREE-binder dependent Π `(head : A) → (tail : List A) → (rec : motive tail) → motive (cons head
tail)` whose ι reduct is an app spine (Π-form, not nat's substituted binder-form).  Same `subst_compose` +
`subst_pointwise` discipline as nat / either, the depth-3 codomain reconciled via `tripleWeaken_eq_substShiftBy3`
and the depth-2 rec-binder type via nat's `doubleWeaken_eq_substShiftBy2`. -/

#assert_no_axioms FX1Poly.Typed.tripleWeaken_eq_substShiftBy3
#assert_no_axioms FX1Poly.Typed.listElimDependentConsBranchCodomain
#assert_no_axioms FX1Poly.Typed.subst_listElimDependentConsBranchCodomain_consIota
#assert_no_axioms FX1Poly.Typed.subst_listElimDependentConsBranchCodomain_general
#assert_no_axioms FX1Poly.Typed.subst_listElimDependentConsBranchCodomain_substLiftLiftLift
#assert_no_axioms FX1Poly.Typed.subst_listElimDependentConsBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.rename_listElimDependentConsBranchCodomain_iterateLift
#assert_no_axioms FX1Poly.Typed.listElimDependentRecBinderType
#assert_no_axioms FX1Poly.Typed.subst_listElimDependentRecBinderType_substLiftLift
#assert_no_axioms FX1Poly.Typed.subst_listElimDependentRecBinderType_iterateLift
#assert_no_axioms FX1Poly.Typed.rename_listElimDependentRecBinderType_iterateLift
#assert_no_axioms FX1Poly.Typed.listElimDependentConsBranchType

/-! ## Per-table substitution stability (the table-driven-arm legs) -/

#assert_no_axioms FX1Poly.Typed.baseTypeRuleDescOf_outputSubstStable
#assert_no_axioms FX1Poly.Typed.dataIntroNullaryRuleDescOf_outputSubstStable
#assert_no_axioms FX1Poly.Typed.FlatDescTelescopePi.substRespectingTelescope

/-! ## (1) ★ The pointwise substitution lemma over the union + the binder-check transport -/

#assert_no_axioms FX1Poly.Typed.gradedBinderChecks_subst_lift
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substRespectingContext

/-! ## (2) ★ The 2-variable corollaries -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substPairUnderTwoBindings
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substPairNonDependent

/-! ## (3) ★★ The general succ-branch recursive-eliminator ι discharge -/

#assert_no_axioms FX1Poly.Typed.natElimRecursiveCallUnionTyped
#assert_no_axioms FX1Poly.Typed.natRecRecursiveCallUnionTyped
#assert_no_axioms FX1Poly.Typed.natElimSuccIotaComputesTypedInUnion
#assert_no_axioms FX1Poly.Typed.natRecSuccIotaComputesTypedInUnion

/-! ## (5) Coverage record + witness -/

#assert_no_axioms FX1Poly.Typed.NativeUnionSubstitutionCoverage
#assert_no_axioms FX1Poly.Typed.nativeUnionSubstitutionCoverageWitness

/-! ## (6) ★ TYTAB-2 formationRule-promotion: the union-obligation toolkit (subst + rename push)

The `formationRule` arm now premises a UNION obligation list; the destructure-and-rebuild consumers
(substitution / weakening) push that premise through subst / rename with these generic spine-recursion
lemmas + the union-obligation builder.  The genuine union push-through — no grown telescope. -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.formationRuleOfObligations
#assert_no_axioms FX1Poly.Typed.flatFormationObligations_pushSubst
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations_pushSubst
#assert_no_axioms FX1Poly.Typed.FormationRule.obligations_pushSubst
#assert_no_axioms FX1Poly.Typed.flatFormationObligations_pushRename
#assert_no_axioms FX1Poly.Typed.termIndexedEndpointObligations_pushRename
#assert_no_axioms FX1Poly.Typed.FormationRule.obligations_pushRename

/-! ## (7) ★ TYTAB-2: the UNION-SUBSTITUENT substitution lemmas (the β-family transport, UNCONDITIONAL)

The union-image generalization of `substRespectingContext` — substituent images may be UNION-typed
(`SubstUnionTyped`), so β / endpoint-β / the natElim·natRec succ rows substitute a union-but-not-host
argument into a union body.  The host leg `hostSubstWithUnionImages` (mutual with the formation companion
`baseFormationSubstWithUnionImages` and the telescope companions) lands a host derivation in the union
under union images; the union induction `substRespectingContextUnionImages` threads it through the
`ofGrown` arm; the 1- / 2-binder corollaries are the `subst0` / `cons (singleton)` instantiations.  All
UNCONDITIONAL: the cumulative-former arm closes through the theorem `unionCumulativeFormerCloses` (wave U3
— the five cumulative codes `gen_piTyCode`/`gen_sigmaTyCode`/`gen_listCode`/`gen_optionCode`/`gen_unitCode`
are now `formationRuleOf` rows). -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.cons
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.consTwice
#assert_no_axioms FX1Poly.Typed.DescTelescopeUnion
-- ★ TYTAB-2 wave U3: the cumulative-former oracle, now a THEOREM (β-SR thereby UNCONDITIONAL).
#assert_no_axioms FX1Poly.Typed.cumulativeFormationUnionPremiseToObligations
#assert_no_axioms FX1Poly.Typed.unionCumulativeFormerCloses
#assert_no_axioms FX1Poly.Typed.baseFormationSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.baseTelescopeSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.hostSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.hostTelescopeSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substRespectingContextUnionImages
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.subst0WithUnionImage
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substPairUnderTwoBindingsUnionImages
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substPairNonDependentUnionImages
#assert_no_axioms FX1Poly.Typed.unionSubstPairTransports

end FX1PolyAudit
