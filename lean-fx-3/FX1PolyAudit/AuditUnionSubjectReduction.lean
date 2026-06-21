import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction

/-! # FX1PolyAudit/AuditUnionSubjectReduction — NATIVE-37 part a audit shard (ROOT-redex subject
    reduction for the 24-arm native union)

Per-declaration zero-axiom gate for NATIVE-37 part a + TYTAB-2: the seven unconditional branch-selection ι
subject-reduction theorems (boolElim true/false, natElim/natRec zero, listElim nil, optionMatch none, idJ
refl), the two conditional recursive-succ ι subject-reduction theorems (natElim / natRec succ — re-exposing
the shipped substitution-file theorems), the TYTAB-2 building blocks (the pair-head inversion, the app-row
builder, the recursive listElim-call constructor), the two unconditional projection ι rows (fst/snd pair),
the six conditional substituting / app-chain ι + β rows (option-some, either-inl/inr, β, endpoint-β,
list-cons), the coverage record / witness, the deferred-root-redex-shape predicate, and the total master
dispatcher over `Step` (`unionRootStepSubjectReduction`).  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The seven unconditional branch-selection / projection ι subject-reduction theorems -/

#assert_no_axioms FX1Poly.Typed.unionSubjectReductionBoolElimTrue
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionBoolElimFalse
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatElimZero
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatRecZero
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionListElimNil
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionOptionMatchNone
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionIdJRefl

/-! ## The two recursive-succ ι subject-reduction theorems (W4: residual = the cumulative-former oracle).
After TYTAB-2 W4 these take `UnionCumulativeFormerCloses` (the precise, documented cumulative-former wall)
in place of the whole `UnionSubstPairTransports` transport — the natElim·natRec succ substitution is now
the shipped `substPairNonDependentUnionImages`, conditional only on forming the four cumulative type-codes
from union children. -/

#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatElimSucc
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionNatRecSucc

/-! ## TYTAB-2: the local building blocks (the pair-head inversion + the four data-constructor
introducer-head inversions + the app-row builder + the recursive-call constructor + the element
reclassification residual) -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtPairHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtOptionSomeHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtEitherInlHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtEitherInrHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtListConsHead
#assert_no_axioms FX1Poly.Typed.unionAppCellTyped
#assert_no_axioms FX1Poly.Typed.listElimRecursiveCallUnionTyped
#assert_no_axioms FX1Poly.Typed.UnionElementReclassifies

/-! ## TYTAB-2: the two unconditional projection ι subject-reduction theorems -/

#assert_no_axioms FX1Poly.Typed.unionSubjectReductionFstPair
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionSndPair

/-! ## TYTAB-2: the six conditional substituting / app-chain ι + β subject-reduction theorems.
The four app-chain selectors (option-some, either-inl/inr, list-cons) are now GENUINE-except-residual:
their SOLE typing input is the redex typing (handler + payload typings DERIVED via the eliminator-head
inversion + the new data-constructor introducer-head inversions), leaving only the lone
`UnionElementReclassifies` residual (the no-validity / type-Conv-closure gap — value reclassification across
the Conv-equal element types, the same wall the host `piElimUpToClassifierConv` factors out).  β / endpoint-β
(W4) now substitute the union argument via the shipped `subst0WithUnionImage`, conditional only on the
precise cumulative-former oracle `UnionCumulativeFormerCloses` (via `unionSubst0Transports_ofFormerCloses`)
— strictly smaller than the whole 1-binder-substitution transport they held before W4. -/

#assert_no_axioms FX1Poly.Typed.unionSubjectReductionOptionMatchSome
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionEitherMatchInl
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionEitherMatchInr
#assert_no_axioms FX1Poly.Typed.unionSubst0Transports_ofFormerCloses
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionBeta
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionEndpointBeta
#assert_no_axioms FX1Poly.Typed.unionSubjectReductionListElimCons

/-! ## Coverage record + witness -/

#assert_no_axioms FX1Poly.Typed.NativeUnionRootRedexSubjectReductionCoverage
#assert_no_axioms FX1Poly.Typed.nativeUnionRootRedexSubjectReductionCoverageWitness

/-! ## The deferred-shape predicate + the total master dispatcher over `Step` -/

#assert_no_axioms FX1Poly.Typed.IsDeferredRootRedexShape
#assert_no_axioms FX1Poly.Typed.unionRootStepSubjectReduction

end FX1PolyAudit
