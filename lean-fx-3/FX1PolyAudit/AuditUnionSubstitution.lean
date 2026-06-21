import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionUnionSubstituent

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
#assert_no_axioms FX1Poly.Typed.subst_nonDependentArrow

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

/-! ## (7) ★ TYTAB-2 W4: the UNION-SUBSTITUENT substitution lemmas (the β-family transport discharge)

The union-image generalization of `substRespectingContext` — substituent images may be UNION-typed
(`SubstUnionTyped`), so β / endpoint-β / the natElim·natRec succ rows substitute a union-but-not-host
argument into a union body.  The host leg `hostSubstWithUnionImages` (mutual with the formation companion
`baseFormationSubstWithUnionImages` and the telescope companions) lands a host derivation in the union
under union images; the union induction `substRespectingContextUnionImages` threads it through the
`ofGrown` arm; the 1- / 2-binder corollaries are the `subst0` / `cons (singleton)` instantiations.  All
conditional ONLY on the precise cumulative-former oracle `UnionCumulativeFormerCloses` (the documented
`UnionDataFormerValidity` wall — forming `gen_piTyCode`/`gen_sigmaTyCode`/`gen_listCode`/`gen_optionCode`
from union children), strictly smaller than the whole-transport residual the β-family rows held before. -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.cons
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.SubstUnionTyped.consTwice
#assert_no_axioms FX1Poly.Typed.DescTelescopeUnion
#assert_no_axioms FX1Poly.Typed.baseFormationSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.baseTelescopeSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.hostSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.hostTelescopeSubstWithUnionImages
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substRespectingContextUnionImages
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.subst0WithUnionImage
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substPairUnderTwoBindingsUnionImages
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.substPairNonDependentUnionImages
#assert_no_axioms FX1Poly.Typed.unionSubstPairTransports_ofFormerCloses

end FX1PolyAudit
