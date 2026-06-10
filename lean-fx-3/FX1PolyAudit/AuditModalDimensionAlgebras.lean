import FX1PolyAudit.DependencyAudit
import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradeVector
import FX1Poly.Modal.GradeVectorGeneric
import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradedGradeExactness
import FX1Poly.Modal.GradeErasureGeneric
import FX1Poly.Modal.GradedWeakeningGeneric
import FX1Poly.Modal.GradedSubstitutionGeneric
import FX1Poly.Modal.GradedSubjectReductionGeneric
import FX1Poly.Modal.GradedCompositionGeneric
import FX1Poly.Modal.GradeSemiringProduct
import FX1Poly.Modal.GradeSemiringMonoidal
import FX1Poly.Modal.GradeSemiringFunctorial
import FX1Poly.Modal.SimpleStrongNormalization
import FX1Poly.Modal.GradedSubstitutionAlgebra
import FX1Poly.Modal.GradedReductionSubstitution
import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Modal.GradedReductionConfluence
import FX1Poly.Modal.GradedNormalization
import FX1Poly.Modal.ComplexitySemiring
import FX1Poly.Modal.EffectLatticeClassification
import FX1Poly.Modal.OverflowLatticeDimension
import FX1Poly.Modal.PrecisionOverflowCollision
import FX1Poly.Modal.SoundnessCollisionSchema
import FX1Poly.Modal.ThreeWayCollisionClassifiedAsyncSession
import FX1Poly.Modal.FlagshipMultiDimensionSignature
import FX1Poly.Modal.SoundnessCollisionCatalog
import FX1Poly.Modal.SoundnessCollisionCatalogComplete
import FX1Poly.Modal.BoundedJoinSemilatticeUniversal
import FX1Poly.Modal.BoundedJoinSemilatticeProductOrder
import FX1Poly.Modal.UnifiedGradeMonoid
import FX1Poly.Modal.FractionalPermission
import FX1Poly.Modal.ClockDomainLatticeDimension
import FX1Poly.Modal.ProvenanceLatticeDimension
import FX1Poly.Modal.MutationChainLatticeDimension
import FX1Poly.Modal.PreorderDimension
import FX1Poly.Modal.DimensionRepetitionContrast
import FX1Poly.Modal.DimensionMultiplicationContrast
import FX1Poly.Modal.LatticeDistributivityClassification
import FX1Poly.Modal.SessionDualityDimension
import FX1Poly.Modal.SessionCommunication
import FX1Poly.Modal.SelfApplicationUntypable
import FX1Poly.Modal.GradedProgress
import FX1Poly.Modal.GradedEvaluation
import FX1Poly.Modal.GradedLogicalConsistency
import FX1Poly.Modal.VersionCategoryDimension
import FX1Poly.Modal.GradedNormalizerValue

/-! # FX1PolyAudit/AuditModalDimensionAlgebras — modal/dimension-layer zero-axiom gates, shard 1 of 4 (split from the AuditModal monolith for parallel gate elaboration) -/

/-! # FX1PolyAudit/AuditModal — per-declaration zero-axiom gate for the resource-graded doctrine
   (the second graded dimension: Usage `{0, 1, ω}` and Security `{unclassified < classified}`)

`FX1Poly.Modal.ResourceGraded` is the substrate for FX's usage dimension — the first graded
dimension beyond Type (§6.1).  The usage grade algebra `{0, 1, ω}` is proven a genuine ORDERED
SEMIRING (`IsLawfulOrderedGradeSemiring fxUsageSemiring`): commutative-monoid `+`, monoid `*`,
distributivity, annihilation, and a partial order compatible with both operations.

Each gate fails the build if its declaration depends on `propext` / `Quot.sound` / `Classical` /
`sorry` / `native_decide` / `omega`, holding the `ResourceGraded` surface to the same
per-declaration discipline as the rest of the kernel.
-/

/-! ### Grade-algebra substrate (the ordered-semiring data bundle + the two instances) -/

#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring
#assert_no_axioms FX1Poly.Modal.UsageGrade
#assert_no_axioms FX1Poly.Modal.UsageGrade.add
#assert_no_axioms FX1Poly.Modal.UsageGrade.mul
#assert_no_axioms FX1Poly.Modal.UsageGrade.le
#assert_no_axioms FX1Poly.Modal.fxUsageSemiring
#assert_no_axioms FX1Poly.Modal.SecurityGrade
#assert_no_axioms FX1Poly.Modal.SecurityGrade.add
#assert_no_axioms FX1Poly.Modal.SecurityGrade.mul
#assert_no_axioms FX1Poly.Modal.SecurityGrade.le
#assert_no_axioms FX1Poly.Modal.fxSecuritySemiring

/-! ### Usage trivial-fragment laws (identity / annihilation / add-commutativity) -/

#assert_no_axioms FX1Poly.Modal.UsageGrade.add_comm
#assert_no_axioms FX1Poly.Modal.UsageGrade.add_zero
#assert_no_axioms FX1Poly.Modal.UsageGrade.zero_add
#assert_no_axioms FX1Poly.Modal.UsageGrade.mul_one
#assert_no_axioms FX1Poly.Modal.UsageGrade.one_mul
#assert_no_axioms FX1Poly.Modal.UsageGrade.mul_zero
#assert_no_axioms FX1Poly.Modal.UsageGrade.zero_mul
#assert_no_axioms FX1Poly.Modal.UsageGrade.linear_div_omega_eq_zero

/-! ### Usage core semiring laws (associativity / commutativity / distributivity) -/

#assert_no_axioms FX1Poly.Modal.UsageGrade.add_assoc
#assert_no_axioms FX1Poly.Modal.UsageGrade.mul_assoc
#assert_no_axioms FX1Poly.Modal.UsageGrade.mul_comm
#assert_no_axioms FX1Poly.Modal.UsageGrade.left_distrib
#assert_no_axioms FX1Poly.Modal.UsageGrade.right_distrib

/-! ### Usage order laws (the "ordered" part of the ordered semiring) -/

#assert_no_axioms FX1Poly.Modal.UsageGrade.le_refl
#assert_no_axioms FX1Poly.Modal.UsageGrade.le_trans
#assert_no_axioms FX1Poly.Modal.UsageGrade.le_antisymm
#assert_no_axioms FX1Poly.Modal.UsageGrade.add_le_add_left
#assert_no_axioms FX1Poly.Modal.UsageGrade.mul_le_mul_left

/-! ### The verified-semiring bundle + the usage witness -/

#assert_no_axioms FX1Poly.Modal.IsLawfulOrderedGradeSemiring
#assert_no_axioms FX1Poly.Modal.fxUsageSemiring_isLawful

/-! ### Security grade-algebra laws + the verified-semiring witness (a second graded dimension) -/

#assert_no_axioms FX1Poly.Modal.SecurityGrade.add_comm
#assert_no_axioms FX1Poly.Modal.SecurityGrade.add_assoc
#assert_no_axioms FX1Poly.Modal.SecurityGrade.add_zero
#assert_no_axioms FX1Poly.Modal.SecurityGrade.zero_add
#assert_no_axioms FX1Poly.Modal.SecurityGrade.mul_assoc
#assert_no_axioms FX1Poly.Modal.SecurityGrade.mul_one
#assert_no_axioms FX1Poly.Modal.SecurityGrade.one_mul
#assert_no_axioms FX1Poly.Modal.SecurityGrade.mul_zero
#assert_no_axioms FX1Poly.Modal.SecurityGrade.zero_mul
#assert_no_axioms FX1Poly.Modal.SecurityGrade.mul_comm
#assert_no_axioms FX1Poly.Modal.SecurityGrade.left_distrib
#assert_no_axioms FX1Poly.Modal.SecurityGrade.right_distrib
#assert_no_axioms FX1Poly.Modal.SecurityGrade.le_refl
#assert_no_axioms FX1Poly.Modal.SecurityGrade.le_trans
#assert_no_axioms FX1Poly.Modal.SecurityGrade.le_antisymm
#assert_no_axioms FX1Poly.Modal.SecurityGrade.add_le_add_left
#assert_no_axioms FX1Poly.Modal.SecurityGrade.mul_le_mul_left
#assert_no_axioms FX1Poly.Modal.SecurityGrade.classified_poisons_add
#assert_no_axioms FX1Poly.Modal.fxSecuritySemiring_isLawful
-- DIM-PRODUCT (#1035): §6 "Product of all forms the grade vector". OrderedGradeSemiring.product is the
-- componentwise product; IsLawfulOrderedGradeSemiring.product (★) proves the 16 ordered-semiring laws of the
-- product from the factors' (equational laws by Prod.ext, order laws by propext-free Bool-AND helpers). So
-- lawfulness is preserved under product, and the generic metatheory (which consumes exactly a lawfulness
-- witness) transfers to any composite dimension. fxUsageTimesSecuritySemiring = usage{0,1,ω} × security
-- {unclass<class}; a variable carries BOTH grades in one judgment; metatheoryFree (★) = SN+SR for the
-- composed dimension FOR FREE (metatheoryBundle ∘ product-lawful), generalizing DIM2-7/#880 to a product.
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.product
#assert_no_axioms FX1Poly.Modal.IsLawfulOrderedGradeSemiring.product
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecuritySemiring_isLawful
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurity_one_isPair
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurity_variableCarriesBothGrades
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurity_metatheoryFree
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurity_appliedIdentity_metatheoryFree
-- DIM-PRODUCT-MONOIDAL (#1036): the grade-semiring product is SYMMETRIC MONOIDAL — commutative and associative
-- up to STRICT grade-semiring isomorphism, so "product of all forms the grade vector" is well-defined for N≥3
-- dimensions regardless of order/grouping. swapGrade (★): product A B ≅ product B A, preserving zero/one/add/mul
-- (rfl) + le (Bool-AND comm) + involutive. assocGrade/unassocGrade: product (product A B) C ≅ product A (product
-- B C), operations rfl + le (Bool-AND assoc) + mutually inverse. fxUsageTimesSecurityTimesComplexity = a concrete
-- 3-dimension instance (usage×security×complexity), lawful by NESTED product + metatheoryFree (★, SN+SR for free).
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.swapGrade_add
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.swapGrade_mul
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.swapGrade_le
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.swapGrade_involutive
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.assocGrade_add
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.assocGrade_mul
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.assocGrade_le
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.assocGrade_unassocGrade
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.unassocGrade_assocGrade
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurityTimesComplexitySemiring_isLawful
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurityTimesComplexity_metatheoryFree
-- DIM-FUNCTORIAL (#1037): the §6 "dimensions checked INDEPENDENTLY/pointwise" content. GTypeOver/GradeVectorOver
-- .mapGrade push grades along f : R.Carrier → S.Carrier; commutation lemmas with zero/single/add/scale + lookup.
-- mapHom (★): a grade-semiring HOMOMORPHISM f (preserving zero/one/add/mul) lifts ANY HasGradeOver R derivation
-- to HasGradeOver S, by 3-arm induction (var via single-commute+fOne+lookup_map, app via add/scale-commute on
-- p1+r·p2) — HasGradeOver is a functor on grade semirings. projectFirst/projectSecond = mapHom at Prod.fst/Prod.snd
-- (the product's projection homs, every law rfl): a 2-dim derivation decomposes into per-dimension derivations.
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.mapGrade_single
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.mapGrade_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.mapGrade_scale
#assert_no_axioms FX1Poly.Modal.GTypeOver.lookup_map
#assert_no_axioms FX1Poly.Modal.HasGradeOver.mapHom
#assert_no_axioms FX1Poly.Modal.HasGradeOver.projectFirst
#assert_no_axioms FX1Poly.Modal.HasGradeOver.projectSecond
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurity_variableProjectsToUsage
#assert_no_axioms FX1Poly.Modal.fxUsageTimesSecurity_variableProjectsToSecurity

/-! ### Grade-vector substrate: the per-binding usage grade vector + its semimodule laws -/

#assert_no_axioms FX1Poly.Modal.GradeVector
#assert_no_axioms FX1Poly.Modal.GradeVector.length
#assert_no_axioms FX1Poly.Modal.GradeVector.zero
#assert_no_axioms FX1Poly.Modal.GradeVector.add
#assert_no_axioms FX1Poly.Modal.GradeVector.scale
#assert_no_axioms FX1Poly.Modal.GradeVector.zero_length
#assert_no_axioms FX1Poly.Modal.GradeVector.scale_length
#assert_no_axioms FX1Poly.Modal.GradeVector.add_comm
#assert_no_axioms FX1Poly.Modal.GradeVector.add_assoc
#assert_no_axioms FX1Poly.Modal.GradeVector.add_zero
#assert_no_axioms FX1Poly.Modal.GradeVector.zero_add
#assert_no_axioms FX1Poly.Modal.GradeVector.scale_zero_scalar
#assert_no_axioms FX1Poly.Modal.GradeVector.scale_one_scalar
#assert_no_axioms FX1Poly.Modal.GradeVector.scale_add
#assert_no_axioms FX1Poly.Modal.GradeVector.scale_scale
#assert_no_axioms FX1Poly.Modal.GradeVector.scale_add_scalar

/-! ### Grade division — the residual of multiplication, feeding the corrected Lam rule -/

#assert_no_axioms FX1Poly.Modal.UsageGrade.div
#assert_no_axioms FX1Poly.Modal.UsageGrade.div_residuation
#assert_no_axioms FX1Poly.Modal.UsageGrade.one_div_omega
#assert_no_axioms FX1Poly.Modal.UsageGrade.div_one
#assert_no_axioms FX1Poly.Modal.UsageGrade.mul_div_le

/-! ### Context division `G / p` (the corrected Lam rule's capture discipline) -/

#assert_no_axioms FX1Poly.Modal.GradeVector.contextDivide
#assert_no_axioms FX1Poly.Modal.GradeVector.contextDivide_length
#assert_no_axioms FX1Poly.Modal.GradeVector.IsPointwiseBelow
#assert_no_axioms FX1Poly.Modal.GradeVector.scale_contextDivide_below

/-! ### Grade-vector order: IsPointwiseBelow partial order + monotonicity + the Galois connection -/

#assert_no_axioms FX1Poly.Modal.UsageGrade.add_le_add
#assert_no_axioms FX1Poly.Modal.GradeVector.IsPointwiseBelow.refl
#assert_no_axioms FX1Poly.Modal.GradeVector.IsPointwiseBelow.trans
#assert_no_axioms FX1Poly.Modal.GradeVector.IsPointwiseBelow.antisymm
#assert_no_axioms FX1Poly.Modal.GradeVector.IsPointwiseBelow.scale_mono
#assert_no_axioms FX1Poly.Modal.GradeVector.IsPointwiseBelow.add_mono
#assert_no_axioms FX1Poly.Modal.GradeVector.contextDivide_residuation

/-! ### Var-rule singleton + binder stripping (single / tail) -/

#assert_no_axioms FX1Poly.Modal.GradeVector.single
#assert_no_axioms FX1Poly.Modal.GradeVector.tail
#assert_no_axioms FX1Poly.Modal.GradeVector.single_length

/-! ### The usage grade check + the Atkey-2018 broken-Lam rejection (§27.1 / §27.2) -/

#assert_no_axioms FX1Poly.Modal.GradedLambda
#assert_no_axioms FX1Poly.Modal.GradedLambda.usage
#assert_no_axioms FX1Poly.Modal.GradedLambda.WellGraded
#assert_no_axioms FX1Poly.Modal.atkeyClosure
#assert_no_axioms FX1Poly.Modal.linearClosure
#assert_no_axioms FX1Poly.Modal.linearContext
#assert_no_axioms FX1Poly.Modal.atkey_usage
#assert_no_axioms FX1Poly.Modal.linear_usage
#assert_no_axioms FX1Poly.Modal.atkey_rejected
#assert_no_axioms FX1Poly.Modal.linear_accepted

/-! ### The usage check as a verified Boolean decision procedure -/

#assert_no_axioms FX1Poly.Modal.GradeVector.isPointwiseBelowBool
#assert_no_axioms FX1Poly.Modal.GradeVector.isPointwiseBelowBool_correct
#assert_no_axioms FX1Poly.Modal.GradedLambda.wellGradedCheck
#assert_no_axioms FX1Poly.Modal.GradedLambda.wellGradedCheck_correct
#assert_no_axioms FX1Poly.Modal.atkey_check_false
#assert_no_axioms FX1Poly.Modal.linear_check_true

/-! ### Naive occurrence check fails subject reduction — the (λx.x x) g counterexample (§27.2/§27.3) -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.shift
#assert_no_axioms FX1Poly.Modal.GradedLambda.substAt
#assert_no_axioms FX1Poly.Modal.GradedLambda.BetaStep
#assert_no_axioms FX1Poly.Modal.dupRedex
#assert_no_axioms FX1Poly.Modal.dupReduct
#assert_no_axioms FX1Poly.Modal.linearG
#assert_no_axioms FX1Poly.Modal.dupRedex_beta
#assert_no_axioms FX1Poly.Modal.dupRedex_wellGraded
#assert_no_axioms FX1Poly.Modal.dupReduct_illGraded
#assert_no_axioms FX1Poly.Modal.usage_check_fails_subject_reduction

/-! ### Generic grade-vector substrate over any OrderedGradeSemiring (security + dims 6–21) -/

#assert_no_axioms FX1Poly.Modal.GradeVectorOver
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.length
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.scale
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.zero_length
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.scale_length
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.add_comm
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.add_assoc
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.add_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.zero_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.scale_zero_scalar
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.scale_one_scalar
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.scale_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.scale_scale
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.scale_add_scalar
#assert_no_axioms FX1Poly.Modal.IsLawfulOrderedGradeSemiring.add_le_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.IsPointwiseBelow
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.IsPointwiseBelow.refl
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.IsPointwiseBelow.trans
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.IsPointwiseBelow.antisymm
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.IsPointwiseBelow.scale_mono
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.IsPointwiseBelow.add_mono
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.isPointwiseBelowBool
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.isPointwiseBelowBool_correct
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.single
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.tail
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.single_length
#assert_no_axioms FX1Poly.Modal.usageGradeVector_scale_add
#assert_no_axioms FX1Poly.Modal.securityGradeVector_add_comm
#assert_no_axioms FX1Poly.Modal.securityGradeVector_below_refl

