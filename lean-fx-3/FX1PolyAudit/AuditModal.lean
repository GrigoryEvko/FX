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

/-! ### The GENERIC graded typing judgment over any OrderedGradeSemiring (security + dims 6–21)

`HasGradeOver R` — the §6.2 grade-checking judgment (corrected Wood/Atkey Lam + App scaling), generic
over the ordered semiring, on the generic grade vector.  Structural metatheory (3 inversions + the
length-coherence invariant) is generic over R.  The witnesses type the linear identity + K combinator
at BOTH usage and security — the orthogonal-composition thesis at the JUDGMENT layer. -/

#assert_no_axioms FX1Poly.Modal.GTypeOver
#assert_no_axioms FX1Poly.Modal.GTypeOver.lookup
#assert_no_axioms FX1Poly.Modal.HasGradeOver
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.add_length_eq
#assert_no_axioms FX1Poly.Modal.HasGradeOver.invertVar
#assert_no_axioms FX1Poly.Modal.HasGradeOver.invertLam
#assert_no_axioms FX1Poly.Modal.HasGradeOver.invertApp
#assert_no_axioms FX1Poly.Modal.hasGradeOver_length
#assert_no_axioms FX1Poly.Modal.linearIdentityOver_typed
#assert_no_axioms FX1Poly.Modal.kCombinatorOver_typed
#assert_no_axioms FX1Poly.Modal.usageLinearIdentity_typedViaGeneric
#assert_no_axioms FX1Poly.Modal.securityLinearIdentity_typedViaGeneric
#assert_no_axioms FX1Poly.Modal.securityKCombinator_typedViaGeneric

/-! ### Grade EXACTNESS — the synthesised binder grade is forced, not chosen (grade honesty)

The CONVERSE of the positive `linearIdentityOver_typed` / `kCombinatorOver_typed` witnesses: a derivation
pins the binder grade EXACTLY (no subsumption rule ⟹ grades are synthesised).  `identityBinderGradeForcedOne`
= `λx.x : base-(g)->base` forces `g = R.one` (use is exact); `kSecondBinderGradeForcedZero` = `λx.λy.x`
forces the dropped `g₂ = R.zero` (discard is exact).  `usage`/`securityIdentityNotDiscardable` = the
concrete payoff: the identity cannot be typed as a discard (grade `R.zero`) because that forces `0 = 1`,
refuted by `UsageGrade`/`SecurityGrade` no-confusion — grade forgery is structurally rejected. -/

#assert_no_axioms FX1Poly.Modal.identityBinderGradeForcedOne
#assert_no_axioms FX1Poly.Modal.kSecondBinderGradeForcedZero
#assert_no_axioms FX1Poly.Modal.usageIdentityNotDiscardable
#assert_no_axioms FX1Poly.Modal.securityIdentityNotDiscardable

/-! ### Generic grade erasure + SN-transfer over any OrderedGradeSemiring (security + dims 6–21)

`HasGradeOver R` erases to the grade-free `HasSimpleType`, so STLC strong normalization (the Tait
fundamental theorem) transfers to the generic judgment for ANY dimension R — no graded-reducibility
re-proof.  The orthogonal-composition thesis (SN survives erasure) at the judgment layer for all 21
dimensions at once. -/

#assert_no_axioms FX1Poly.Modal.eraseGTypeOver
#assert_no_axioms FX1Poly.Modal.lookup_map_eraseGTypeOver
#assert_no_axioms FX1Poly.Modal.HasGradeOver.erase
#assert_no_axioms FX1Poly.Modal.HasGradeOver.stronglyNormalizing
#assert_no_axioms FX1Poly.Modal.linearIdentityOver_stronglyNormalizing
#assert_no_axioms FX1Poly.Modal.securityLinearIdentity_stronglyNormalizingViaGeneric
#assert_no_axioms FX1Poly.Modal.securityKCombinator_stronglyNormalizingViaGeneric

/-! ### DIM3: the complexity / space N-semiring — the THIRD graded dimension over `HasGradeOver`

The unbounded, non-idempotent-`+` `Nat` semiring (§6.3 dim 13 / dim 15), after usage `{0,1,ω}` and security
`{unclass<class}`.  `complexityAddNotIdempotent` (`1+1 != 1`) marks it a genuinely NEW semiring shape; its
`mul_assoc`/`right_distrib` are hand-rolled axiom-clean (`natMulAssoc`/`natRightDistrib`) since the stdlib
`Nat.mul_assoc`/`Nat.right_distrib` leak propext.  SN transfers to the third dimension for FREE via
`complexityLinearIdentity_stronglyNormalizingViaGeneric` — the orthogonal-composition thesis, no per-dimension
SN proof. -/

#assert_no_axioms FX1Poly.Modal.natBle_self
#assert_no_axioms FX1Poly.Modal.natMulComm
#assert_no_axioms FX1Poly.Modal.natMulAssoc
#assert_no_axioms FX1Poly.Modal.natRightDistrib
#assert_no_axioms FX1Poly.Modal.fxComplexitySemiring
#assert_no_axioms FX1Poly.Modal.fxComplexitySemiring_isLawful
#assert_no_axioms FX1Poly.Modal.complexityAddNotIdempotent
#assert_no_axioms FX1Poly.Modal.complexityLinearIdentity_typed
#assert_no_axioms FX1Poly.Modal.complexityLinearIdentity_stronglyNormalizingViaGeneric

/-! ### The EFFECT-family boundary: bounded join-semilattice, NOT an ordered grade semiring

Which dimensions the generic `HasGradeOver` semiring engine COVERS, formally delimited.  The resource /
co-effect dims (usage, security, complexity/space/precision) are ordered semirings (distinct annihilating
`mul`); the EFFECT family is a bounded join-semilattice (single idempotent op, no annihilator), so it does NOT
fit — `effectIsNotLawfulOrderedGradeSemiring` proves the §9.3 monotone-accumulation `mul = join` has no
annihilator (`join impure pure = impure ≠ pure`), upgrading the informal DIM5-era memory note to a theorem.
`effectIsLawfulBoundedJoinSemilattice` is the positive structure; `gradeAlgebraOf` is the classification. -/
#assert_no_axioms FX1Poly.Modal.EffectGrade
#assert_no_axioms FX1Poly.Modal.EffectGrade.join
#assert_no_axioms FX1Poly.Modal.EffectGrade.le
#assert_no_axioms FX1Poly.Modal.effectSemiringCandidate
#assert_no_axioms FX1Poly.Modal.effectJoinAnnihilation_concretelyFails
#assert_no_axioms FX1Poly.Modal.effectIsNotLawfulOrderedGradeSemiring
#assert_no_axioms FX1Poly.Modal.securityHasAnnihilation
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.IsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.effectLattice
#assert_no_axioms FX1Poly.Modal.effectIsLawfulBoundedJoinSemilattice
-- The TRUST dual (order-dual of effect: add = mul = weakest-link min): TrustGrade + weakestLink + le; the
-- negative result trustIsNotLawfulOrderedGradeSemiring (min has no annihilator, mirror of effect) + the
-- positive trustIsLawfulBoundedJoinSemilattice. Upgrades the trust dimension from "classified by analogy" to a
-- machine-checked proof on par with effect, so BOTH semilattice-family dims are now proven (closes the
-- DIM-CLASS trust hand-wave). Full 2x2 enumeration / decide, propext-free.
#assert_no_axioms FX1Poly.Modal.TrustGrade
#assert_no_axioms FX1Poly.Modal.TrustGrade.weakestLink
#assert_no_axioms FX1Poly.Modal.TrustGrade.le
#assert_no_axioms FX1Poly.Modal.trustSemiringCandidate
#assert_no_axioms FX1Poly.Modal.trustWeakestLinkAnnihilation_concretelyFails
#assert_no_axioms FX1Poly.Modal.trustIsNotLawfulOrderedGradeSemiring
#assert_no_axioms FX1Poly.Modal.trustLattice
#assert_no_axioms FX1Poly.Modal.trustIsLawfulBoundedJoinSemilattice
-- Lattice-family COMPOSITION (the §1.3/§6.8 "dimensions compose" thesis for the lattice family, analogue of the
-- resource grade vector): BoundedJoinSemilattice.product (pointwise product) + productIsLawful (product of two
-- LAWFUL lattices is lawful, every law componentwise, no re-proof) + the concrete effectTrustProductLattice +
-- effectTrustProductIsLawful witness (two real §6.8 lattice dims compose). pairEqOfComponents = the Init-only
-- pair-congruence glue (no congrArg2 outside Mathlib). All zero-axiom.
#assert_no_axioms FX1Poly.Modal.pairEqOfComponents
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.product
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.productIsLawful
#assert_no_axioms FX1Poly.Modal.effectTrustProductLattice
#assert_no_axioms FX1Poly.Modal.effectTrustProductIsLawful
-- The induced partial ORDER (the algebra recovers the §6.3 dimension order): BoundedJoinSemilattice.le (lower ≤
-- upper iff join = upper) + le_refl/le_trans/le_antisymm/bottom_le (the partial-order laws DERIVED from the join
-- laws, not separate axioms) + effectLe_pure_impure (the §6.3 effect order Tot ≤ impure) + trustLe_trusted_
-- untrusted (the trust dual order). Shows the spec's order presentation of each lattice dimension agrees with
-- its algebra. All zero-axiom (calc via the shipped join laws).
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.le
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.le_refl
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.le_trans
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.le_antisymm
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.bottom_le
#assert_no_axioms FX1Poly.Modal.effectLe_pure_impure
#assert_no_axioms FX1Poly.Modal.trustLe_trusted_untrusted
-- The OVERFLOW dimension (§6.3 Dim 16, OverflowLatticeDimension.lean) — the FIRST NON-CHAIN bounded
-- join-semilattice: the diamond M3 (exactGrade bottom; wrap/trap/saturate ANTICHAIN; conflictGrade top = the
-- "mixing overflow modes is a type error" rejected state). OverflowGrade (5-ctor) + join (25-case diamond) +
-- overflowLattice + overflowIsLawfulBoundedJoinSemilattice (laws by cases-rfl, incl. 125-leaf assoc). The
-- conflict-mixing facts overflowJoin_{wrap_trap,wrap_saturate,trap_saturate} (any two distinct modes join to
-- conflict, rfl). The genuinely-new NON-CHAIN content: overflow{WrapTrap,WrapSaturate,TrapSaturate}Incomparable
-- (the 3 modes pairwise incomparable in the induced order — no chain lattice has this; the engine's antisymmetric
-- le exercised on a real antichain), via the defeq noConfusion route. overflowConflictIsGreatest (top) +
-- overflowExactIsLeast (bottom via generic bottom_le). overflowEffectProductLattice + overflowEffectProductIsLawful
-- (a NON-CHAIN dim composes with a CHAIN dim via the shipped productIsLawful, no re-proof — composition is
-- shape-agnostic). All zero-axiom (full-enum match + cases-rfl + noConfusion + reused productIsLawful, no funext).
#assert_no_axioms FX1Poly.Modal.OverflowGrade
#assert_no_axioms FX1Poly.Modal.OverflowGrade.join
#assert_no_axioms FX1Poly.Modal.overflowLattice
#assert_no_axioms FX1Poly.Modal.overflowIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.overflowJoin_wrap_trap
#assert_no_axioms FX1Poly.Modal.overflowJoin_wrap_saturate
#assert_no_axioms FX1Poly.Modal.overflowJoin_trap_saturate
#assert_no_axioms FX1Poly.Modal.overflowWrapTrapIncomparable
#assert_no_axioms FX1Poly.Modal.overflowWrapSaturateIncomparable
#assert_no_axioms FX1Poly.Modal.overflowTrapSaturateIncomparable
#assert_no_axioms FX1Poly.Modal.overflowConflictIsGreatest
#assert_no_axioms FX1Poly.Modal.overflowExactIsLeast
#assert_no_axioms FX1Poly.Modal.overflowEffectProductLattice
#assert_no_axioms FX1Poly.Modal.overflowEffectProductIsLawful
-- The overflow MEET — completing the diamond M3 to the kernel's FIRST FULL bounded lattice
-- (OverflowLatticeDimension.lean, bottom). OverflowGrade.meet (diamond infimum, dual to join: conflict top is the
-- meet identity, distinct modes meet DOWN to the exact bottom) + meet-semilattice laws (comm/assoc/idempotent/
-- top-identity/exact-absorb, the cases<;>rfl mirror of the join laws) + the two ABSORPTION laws (join a (meet a b)
-- = a / meet a (join a b) = a) that upgrade two semilattices into a genuine bounded LATTICE — the kernel's first
-- full lattice (every prior dim built only the join half). Dual conflict-mixing (overflowMeet_{wrap_trap,
-- wrap_saturate,trap_saturate} = exact). THE TWO HEADLINES: overflowIsNonDistributive (canonical M3 failure
-- wrap∧(trap∨saturate)=wrap ≠ exact=(wrap∧trap)∨(wrap∧saturate), by decide — overflow is richer than the
-- distributive chains) + overflowIsModular (a≤c → a∨(b∧c)=(a∨b)∧c holds, the le-guard's impossible cases refuted
-- by noConfusion) — pinning overflow precisely as M3 (diamond, modular non-distributive), NOT N5 (pentagon,
-- non-modular). All zero-axiom (cases<;>rfl + decide + noConfusion guard-discharge, no funext/propext).
#assert_no_axioms FX1Poly.Modal.OverflowGrade.meet
#assert_no_axioms FX1Poly.Modal.overflowMeet_comm
#assert_no_axioms FX1Poly.Modal.overflowMeet_assoc
#assert_no_axioms FX1Poly.Modal.overflowMeet_idempotent
#assert_no_axioms FX1Poly.Modal.overflowTopMeet
#assert_no_axioms FX1Poly.Modal.overflowMeetTop
#assert_no_axioms FX1Poly.Modal.overflowExactMeet
#assert_no_axioms FX1Poly.Modal.overflowJoinMeetAbsorb
#assert_no_axioms FX1Poly.Modal.overflowMeetJoinAbsorb
#assert_no_axioms FX1Poly.Modal.overflowMeet_wrap_trap
#assert_no_axioms FX1Poly.Modal.overflowMeet_wrap_saturate
#assert_no_axioms FX1Poly.Modal.overflowMeet_trap_saturate
#assert_no_axioms FX1Poly.Modal.overflowIsNonDistributive
#assert_no_axioms FX1Poly.Modal.overflowIsModular
-- The overflow MEET universal property — meet a b is the GREATEST LOWER BOUND (the glb dual of the shipped lub
-- in BoundedJoinSemilatticeUniversal.lean, completing M3's lattice characterization with BOTH universal
-- properties). overflowMeetLeLeft/Right (meet is a lower bound of each operand) + overflowLeMeet (any common
-- lower bound is dominated by the meet — the greatest part, le-guard impossible cases by noConfusion) +
-- overflowMeetIsGreatestLowerBound (the bundled universal property). Sharp diamond glb corollaries:
-- overflowExactIsGreatestLowerBoundOfWrapTrap (exact is the glb of two distinct modes) +
-- overflowOnlyExactBoundsWrapTrap (THE dual consequence — the ONLY common lower bound of two distinct modes is
-- the exact bottom, mirror of overflowOnlyConflictBoundsWrapTrap: the antichain is pinched to exact below
-- exactly as it escapes to conflict above). All zero-axiom (cases<;>rfl + noConfusion guard-discharge +
-- le_antisymm + the overflowMeet_wrap_trap ▸ rewrite, no funext/propext).
#assert_no_axioms FX1Poly.Modal.overflowMeetLeLeft
#assert_no_axioms FX1Poly.Modal.overflowMeetLeRight
#assert_no_axioms FX1Poly.Modal.overflowLeMeet
#assert_no_axioms FX1Poly.Modal.overflowMeetIsGreatestLowerBound
#assert_no_axioms FX1Poly.Modal.overflowExactIsGreatestLowerBoundOfWrapTrap
#assert_no_axioms FX1Poly.Modal.overflowOnlyExactBoundsWrapTrap
-- The join-semilattice UNIVERSAL PROPERTY + decidable order (BoundedJoinSemilatticeUniversal.lean) — the genuine
-- lattice content the DIM-CLASS-order layer (#912) was missing: le_join_left/le_join_right (join a b is an UPPER
-- bound of both, via assoc+idempotent) + join_le (it is the LEAST upper bound — any common bound dominates it,
-- via assoc) + join_isLeastUpperBound (the three bundled = join a b IS the lub of {a,b}, the defining lattice fact
-- holding for EVERY lattice dimension with no per-dim proof) + decidableLe (the induced order is DECIDABLE
-- straight from carrierDecEq, since le := join=upper). Concrete diamond payoff:
-- overflowConflictIsLeastUpperBoundOfWrapTrap (conflict is the lub of wrap,trap) +
-- overflowOnlyConflictBoundsWrapTrap (THE diamond consequence: the ONLY common upper bound of two distinct modes
-- is the conflict TOP — the precise formalization of §6.3 "mixing overflow modes is a type error", dual to
-- firing-21's antichain). All zero-axiom (calc over the shipped join laws + carrierDecEq + le_antisymm; the ▸
-- rewrite via overflowJoin_wrap_trap; no funext).
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.le_join_left
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.le_join_right
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.join_le
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.join_isLeastUpperBound
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.decidableLe
#assert_no_axioms FX1Poly.Modal.overflowConflictIsLeastUpperBoundOfWrapTrap
#assert_no_axioms FX1Poly.Modal.overflowOnlyConflictBoundsWrapTrap
-- Join MONOTONICITY + the product order is COMPONENTWISE (BoundedJoinSemilatticeProductOrder.lean) — the
-- order-theoretic completion of lattice-family grade-vector composition (product lattice #911 + lub #916 + NOW
-- the product ORDER). join_mono (a≤a', b≤b' ⟹ join a b ≤ join a' b', generic, via le_trans+le_join+join_le —
-- combining stronger grades yields a stronger result) + productLe_iff (THE headline: the product/grade-vector
-- order IS the conjunction of per-dimension orders — §6.2 subsumption decomposes dimension-by-dimension, no
-- cross-dim coupling; forward via congrArg Prod.fst/snd since product le is a pair equality, backward via the
-- shipped pairEqOfComponents — NO Prod.mk.injEq which is propext-backed). Concrete: effectTrustProductLe_iff +
-- overflowEffectProductLe_iff (the latter has the NON-CHAIN overflow diamond as a factor — decomposition is
-- shape-agnostic) + effectTrustVectorSubsumes ((pure,trusted)≤(impure,untrusted) via both components). All
-- zero-axiom (composed order/lub lemmas + congrArg + pairEqOfComponents, no funext, no propext).
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.join_mono
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.productLe_iff
#assert_no_axioms FX1Poly.Modal.effectTrustProductLe_iff
#assert_no_axioms FX1Poly.Modal.overflowEffectProductLe_iff
#assert_no_axioms FX1Poly.Modal.effectTrustVectorSubsumes
-- The UNIFIED grade VECTOR across BOTH families (UnifiedGradeMonoid.lean) — the honest §1.3/§6.1/§6.8 "21
-- dimensions compose", resolving the §6.1-vs-DIM-CLASS tension: the vector is NOT a pure semiring product
-- (effect/trust aren't semirings) but a product of COMMUTATIVE GRADE MONOIDS (the §6.1 parallel-combine layer
-- both families share). CommutativeGradeMonoid + IsLawful; OrderedGradeSemiring.toCommutativeGradeMonoid (resource
-- dims project, laws = add comm-monoid) + BoundedJoinSemilattice.toCommutativeGradeMonoid (effect-family dims
-- project, laws = join comm-monoid); product + productIsLawful (the vector, componentwise, no re-proof); and the
-- FIRST cross-family witness securityEffectGradeMonoid(+IsLawful) — a semiring dim x a lattice dim in ONE vector.
-- All zero-axiom (record literals + field re-export + the shipped pairEqOfComponents glue).
#assert_no_axioms FX1Poly.Modal.CommutativeGradeMonoid
#assert_no_axioms FX1Poly.Modal.IsLawfulCommutativeGradeMonoid
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.toCommutativeGradeMonoid
#assert_no_axioms FX1Poly.Modal.OrderedGradeSemiring.toCommutativeGradeMonoid_isLawful
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.toCommutativeGradeMonoid
#assert_no_axioms FX1Poly.Modal.BoundedJoinSemilattice.toCommutativeGradeMonoid_isLawful
#assert_no_axioms FX1Poly.Modal.CommutativeGradeMonoid.product
#assert_no_axioms FX1Poly.Modal.CommutativeGradeMonoid.productIsLawful
#assert_no_axioms FX1Poly.Modal.securityEffectGradeMonoid
#assert_no_axioms FX1Poly.Modal.securityEffectGradeMonoidIsLawful
#assert_no_axioms FX1Poly.Modal.DimensionGradeAlgebra
#assert_no_axioms FX1Poly.Modal.GradedDimensionName
#assert_no_axioms FX1Poly.Modal.GradedDimensionName.gradeAlgebraOf
#assert_no_axioms FX1Poly.Modal.usage_isOrderedSemiring
#assert_no_axioms FX1Poly.Modal.security_isOrderedSemiring
#assert_no_axioms FX1Poly.Modal.complexity_isOrderedSemiring
#assert_no_axioms FX1Poly.Modal.effect_isBoundedSemilattice
#assert_no_axioms FX1Poly.Modal.trust_isBoundedSemilattice

/-! ### Generic weakening for HasGradeOver R over any OrderedGradeSemiring (security + dims 6–21)

The de Bruijn weakening metatheory generic over R: `HasGradeOver R` survives `GradedLambda.shift` at
any cut, inserting a `R.zero` grade.  Mirrors the usage `GradedTypingMetatheory`; the App-case grade
arithmetic (`insertAt_add`/`insertAt_scale`) routes through the lawful bundle (`zero_add`/`mul_zero`)
since an abstract semiring's `R.add R.zero R.zero` does not compute.  The prerequisite for generic
substitution → subject reduction. -/

#assert_no_axioms FX1Poly.Modal.insertTypeAtOver
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.insertAt
#assert_no_axioms FX1Poly.Modal.length_insertTypeAtOver
#assert_no_axioms FX1Poly.Modal.lookup_some_ltOver
#assert_no_axioms FX1Poly.Modal.lookup_insertTypeAtOver_lt
#assert_no_axioms FX1Poly.Modal.lookup_insertTypeAtOver_ge
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.insertAt_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.single_insertAt_lt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.single_insertAt_ge
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.insertAt_scale
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.insertAt_add
#assert_no_axioms FX1Poly.Modal.hasGradeOver_weakening

/-! ### Generic substInto grade-algebra over any OrderedGradeSemiring (security + dims 6–21)

The grade transformation β performs, generic over R: `substInto cut q p = removeAt cut p + (gradeAt cut
p)·q`.  Mirrors the usage `GradedSubjectReduction` machinery; the lawful bundle is threaded into the
lemmas whose grade arithmetic an abstract semiring cannot compute (`substInto_succ_cons`,
`gradeAt_scale`/`_add`, `add_interchange`, the `substInto_single_*`/`substInto_appGrade` var/App
identities).  The prerequisite for the generic substitution lemma. -/

#assert_no_axioms FX1Poly.Modal.removeTypeAtOver
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_succ_cons
#assert_no_axioms FX1Poly.Modal.removeTypeAtOver_length
#assert_no_axioms FX1Poly.Modal.lookup_removeTypeAtOver_lt
#assert_no_axioms FX1Poly.Modal.lookup_removeTypeAtOver_ge
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_nil
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_single_ne
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_single_lt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_single_gt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_scale
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_scale
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.add_interchange
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_single_lt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_single_gt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_appGrade

/-! ### Generic substitution + β subject reduction for HasGradeOver R (security + dims 6–21)

The headline of the generic reduction metatheory: substituting at a cut preserves typing with the grade
vector transformed by `substInto`, and β `(λ.body) arg ↝ body[0:=arg]` preserves typing AND the EXACT
grade vector — the corrected Wood/Atkey App scaling making the judgment sound under reduction, for ANY
dimension R.  The security witness exercises β SR in a second dimension. -/

#assert_no_axioms FX1Poly.Modal.hasGradeOver_substitution
#assert_no_axioms FX1Poly.Modal.hasGradeOver_betaPreservation
#assert_no_axioms FX1Poly.Modal.securityBeta_smoke

/-! ### Generic composition ledger for HasGradeOver R (security + dims 6–21)

Graded subject reduction over the FULL β-reduction `Reduces`, and the metatheory bundle (SN ∧ graded-SR
on the same relation, for any dimension R).  The usage ω-witness routes the decisive `ρ + r·σ` regression
(r=ω) through the GENERIC preservedByReduces.  Mirrors the usage `GradedComposition`; completes the
generic reduction metatheory (semiring → vector → judgment → erasure+SN → weakening → substInto →
subst+β-SR → composition). -/

#assert_no_axioms FX1Poly.Modal.HasGradeOver.preservedByReduces
#assert_no_axioms FX1Poly.Modal.HasGradeOver.metatheoryBundle
#assert_no_axioms FX1Poly.Modal.appliedIdentityOver_typed
#assert_no_axioms FX1Poly.Modal.appliedIdentityOver_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.securityAppliedIdentity_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.usageAppliedIdentity_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.securityMetatheoryBundle_smoke
#assert_no_axioms FX1Poly.Modal.omegaScalingBinaryTypeUsage
#assert_no_axioms FX1Poly.Modal.usageOmegaScalingRedex_typed
#assert_no_axioms FX1Poly.Modal.usageOmegaScalingRedex_reductKeepsGrade

/-! ### Grade-free simple typing: the type dimension underneath the graded judgments -/

#assert_no_axioms FX1Poly.Modal.SimpleType
#assert_no_axioms FX1Poly.Modal.SimpleType.lookup
#assert_no_axioms FX1Poly.Modal.HasSimpleType

/-! ### STLC strong normalization substrate: β-reduction + Acc-SN + structural lemmas -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNeutral
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.var
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofAppLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofAppRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofLam
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofReduces

/-! ### Tait reducibility candidates: Reducible + CR1/CR2/CR3 -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible
#assert_no_axioms FX1Poly.Modal.GradedLambda.reducibilityConditions
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.sn
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.ofReduces
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.ofNeutral
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.var

/-! ### Parallel-substitution σ-algebra: renaming + substitution fusion laws

The funext-free de Bruijn substitution infrastructure for the STLC-SN fundamental theorem: a renaming
sublayer makes `lift` compose definitionally, and the four σ-monoid fusion laws + identity drop out
by structural induction with pointwise-agreement congruences (never `funext`/`Quot.sound`). -/

#assert_no_axioms FX1Poly.Modal.incrementIndex
#assert_no_axioms FX1Poly.Modal.liftRenaming
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm
#assert_no_axioms FX1Poly.Modal.liftSubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_congr
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_congr
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.applySubstitution_id

/-! ### Reduction is substitutive: kernel substAt/shift bridge + Reduces.substAt

The kernel `shift`/`substAt` bridged to the σ-algebra, the β-composition (★), and the abstraction-
lemma engine `Reduces.substAt` (single-step β preserved under substitution) + SN-reflection.  Going
through the σ-algebra (rather than a direct de Bruijn substitution-swap) keeps it short: `lift`
composition handles the binder bookkeeping once. -/

#assert_no_axioms FX1Poly.Modal.shiftRenaming
#assert_no_axioms FX1Poly.Modal.shift_eq_renameTerm
#assert_no_axioms FX1Poly.Modal.shift_zero_eq_renameTerm
#assert_no_axioms FX1Poly.Modal.singleSubstitution
#assert_no_axioms FX1Poly.Modal.substAt_eq_applySubstitution
#assert_no_axioms FX1Poly.Modal.consSubstitution
#assert_no_axioms FX1Poly.Modal.substAt_zero_applySubstitution_lift
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.substAt
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofSubstAt

/-! ### Tait SN: the STLC fundamental theorem

The STLC fundamental theorem (abstraction lemma → fundamental → every well-typed term reducible →
SN) proved ONCE.  Graded-SN transfers from this type-dimension SN through grade erasure with no
graded-reducibility re-proof — for ANY dimension R, via the generic `HasGradeOver.stronglyNormalizing`
gated in the generic erasure section above. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.lam
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.abstraction
#assert_no_axioms FX1Poly.Modal.ReducibleSubstitution
#assert_no_axioms FX1Poly.Modal.ReducibleSubstitution.cons
#assert_no_axioms FX1Poly.Modal.HasSimpleType.fundamental
#assert_no_axioms FX1Poly.Modal.HasSimpleType.reducible
#assert_no_axioms FX1Poly.Modal.HasSimpleType.stronglyNormalizing

-- The usage composition ledger (graded-SR over full β + the SN∧graded-SR metatheory bundle + the ω-scaling
-- regression witnesses) is subsumed by the GENERIC HasGradeOver.preservedByReduces / .metatheoryBundle +
-- the usage{Applied,OmegaScaling}* witnesses gated in the generic composition section above.

/-! ### β-confluence infrastructure: reduction-substitutivity for GradedLambda

Part of the full reference STLC (SN + SR + confluence → unique NF).  Reduction under renaming/shift (via
`Reduces.applySubstitution`), multi-step congruence closures, and argument-substitutivity — the inputs to
the local-confluence critical-pair analysis. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_eq_applySubstitution_var
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.shift
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congLam
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.substReducedArg

/-! ### β-confluence: local confluence + Newman → confluence on the typed fragment

The 9-case β critical-pair analysis (`WeaklyConfluent Reduces`), then the relation-generic `newmanAux`
(per-term `Acc` = `IsStronglyNormalizing`) gives confluence on the SN fragment — and hence on every
well-simply-typed `GradedLambda` term (SN from the Tait fundamental theorem). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.localConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.weaklyConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.confluent
#assert_no_axioms FX1Poly.Modal.HasSimpleType.confluent

/-! ### Unique normal forms

Confluence + "a normal form admits no step" ⟹ a strongly-normalizing term has at most one β-NF; hence
every well-simply-typed `GradedLambda` term has a unique normal form (the bridge to decidable
conversion). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm.eq_of_reducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.uniqueNormalForm
#assert_no_axioms FX1Poly.Modal.HasSimpleType.uniqueNormalForm

/-! ### The verified β-normalizer

`stepOrNormal` (β-progress: every term steps-with-witness or is normal) drives `normalize` via `Acc.rec`
on the SN accessibility, producing the unique β-NF bundled with `ReducesStar` reachability and
`IsNormalForm` irreducibility — toward decidable conversion (`normalize a = normalize b`). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.lam_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_app_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.app_app_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.stepOrNormal
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeWithProof
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_reducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_isNormalForm

/-! ### Decidable β-conversion (completes the substrate)

Conversion (`Joinable Reduces`) = normal-form equality on the SN fragment, so it is decidable via
`GradedLambda`'s `DecidableEq` on normal forms.  Every well-simply-typed term pair has decidable
convertibility — the GradedLambda STLC is a full reference calculus with decidable definitional
equality. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofReducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_of_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.joinable_iff_normalize_eq
#assert_no_axioms FX1Poly.Modal.GradedLambda.decidableJoinable
#assert_no_axioms FX1Poly.Modal.HasSimpleType.decidableConv
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_notJoinable_of_ne

/-! ### β-conversion is an equivalence relation (definitional-equality justification)

`Joinable Reduces` is reflexive + symmetric unconditionally, transitive when the middle term is SN
(confluence), and contains reduction — a genuine decidable equivalence on the typed fragment. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.joinable_refl
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.joinable_symm
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.joinable
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.joinable_trans
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.beta_joinable
#assert_no_axioms FX1Poly.Modal.HasSimpleType.joinable_trans

/-! ## §6.4 separation-logic permission algebra — the first PARTIAL grade structure (`FractionalPermission`)

§6.4 makes separation logic an instance of the usage grade: ownership is a fractional share `Frac of p :
rational {0 < p ≤ 1}`, and `Frac(p) + Frac(q) = Frac(p+q)` when `p+q ≤ 1`, else CONFLICT (over-allocation).
This is the FIRST partial grade structure (the shipped graded dims are total ordered semirings / bounded
join-semilattices).  `Permission` (carrier) + the guarded partial `add` + the unguarded buggy `naiveAdd` +
`fitsWhole`; the lawful-monoid fragment (`zero_add` / `add_zero` / `conflict_add` / `add_conflict` /
`add_comm`); the SOUNDNESS theorem `add_neverOverallocates` (combining two fitting shares never yields an
over-full share — the guard prevents over-allocation); and the §27.2 / Boyland-2003 over-allocation BUG
(`naiveAddOverallocates` / `naiveOverallocationDoesNotFit`) vs its REJECTION
(`soundAddRejectsOverallocation`).  ASSOCIATIVITY-where-defined (`add_assoc`, gated by positive outer
denominators `hasPositiveDenom`) closes the fractional core into a genuine lawful PARTIAL commutative monoid
— proved by a triple normal-form argument (both association orders reduce to `bif (triple fits) then triple
else conflict`), with a non-vacuity smoke (`add_assoc_smoke`, `1/4+1/4+1/4`).  All propext-free
(full-enumeration matches, Bool-`bif` guard, `Nat.add_comm`/`Nat.mul_comm`, `injection`/`noConfusion`, `rfl`
witnesses; the cross-multiplied Nat algebra reuses `ComplexitySemiring`'s clean `natMulAssoc`/`natRightDistrib`
— `Nat.mul_assoc`/right-`Nat.add_mul` themselves leak propext). -/

#assert_no_axioms FX1Poly.Modal.Permission.fitsWhole
#assert_no_axioms FX1Poly.Modal.Permission.add
#assert_no_axioms FX1Poly.Modal.Permission.naiveAdd
#assert_no_axioms FX1Poly.Modal.Permission.zero_add
#assert_no_axioms FX1Poly.Modal.Permission.add_zero
#assert_no_axioms FX1Poly.Modal.Permission.conflict_add
#assert_no_axioms FX1Poly.Modal.Permission.add_conflict
#assert_no_axioms FX1Poly.Modal.Permission.add_comm
#assert_no_axioms FX1Poly.Modal.Permission.add_neverOverallocates
#assert_no_axioms FX1Poly.Modal.Permission.naiveAddOverallocates
#assert_no_axioms FX1Poly.Modal.Permission.naiveOverallocationDoesNotFit
#assert_no_axioms FX1Poly.Modal.Permission.soundAddRejectsOverallocation
#assert_no_axioms FX1Poly.Modal.Permission.fracExactlyFullAdmitted
#assert_no_axioms FX1Poly.Modal.Permission.fracExactlyFullFits
#assert_no_axioms FX1Poly.Modal.Permission.fracPartialAdmitted
#assert_no_axioms FX1Poly.Modal.Permission.hasPositiveDenom
#assert_no_axioms FX1Poly.Modal.Permission.add_assoc
#assert_no_axioms FX1Poly.Modal.Permission.add_assoc_smoke

/-! ## §6.3 Dim 12 / §18.7 clock-domain dimension — the first PARAMETERIZED (infinite-carrier) lattice
(`ClockDomainLatticeDimension`)

Every prior lattice dimension (effect/trust/security 2-chains, overflow's finite diamond M3) has a FINITE
enum carrier.  The clock domain `{combinational (bottom), sync (clockId : Nat), crossDomainError (top)}` is
the FIRST with an INFINITE carrier, hence the first INFINITE ANTICHAIN (`sync a` / `sync b` pairwise
incomparable for all distinct clocks).  The parameterized `sync`-`sync` join laws need the three propext-clean
`Nat.beq` facts (`natBeqReflexive` / `natEqOfBeqTrue` / `natBeqCommutes`, hand-rolled by structural
recursion); `clockJoinCommutes` / `clockJoinAssociates` route through them (`Bool.cond_true`/`_false` discharge
the guard residues).  `clockSyncIncomparableOfDistinct` is the genuinely-new infinite-antichain content;
`clockOverflowProductIsLawful` composes the infinite-antichain dimension with the finite diamond via the
shipped `productIsLawful` (cardinality-agnostic composition).  All propext-free; the Nat helpers are gated
transitively by the lattice/antichain theorems but listed explicitly for provenance. -/

#assert_no_axioms FX1Poly.Modal.natBeqReflexive
#assert_no_axioms FX1Poly.Modal.natEqOfBeqTrue
#assert_no_axioms FX1Poly.Modal.natBeqCommutes
#assert_no_axioms FX1Poly.Modal.ClockGrade.join
#assert_no_axioms FX1Poly.Modal.clockJoinSyncWithSelf
#assert_no_axioms FX1Poly.Modal.clockLattice
#assert_no_axioms FX1Poly.Modal.clockJoinCommutes
#assert_no_axioms FX1Poly.Modal.clockJoinAssociates
#assert_no_axioms FX1Poly.Modal.clockIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.clockSyncIncomparableOfDistinct
#assert_no_axioms FX1Poly.Modal.clockSyncJoinDistinctIsCrossDomain
#assert_no_axioms FX1Poly.Modal.clockSync01Incomparable
#assert_no_axioms FX1Poly.Modal.clockCombinationalIsLeast
#assert_no_axioms FX1Poly.Modal.clockCrossDomainIsGreatest
#assert_no_axioms FX1Poly.Modal.clockOverflowProductIsLawful

/-! ## §6.3 Dim 18 mutation dimension — the first proper TOTAL-ORDER chain (`MutationChainLatticeDimension`)

Completes the lattice-shape spanning set: alongside the trivial 2-chains (effect/trust/security), the finite
antichain (overflow M3) and the infinite antichain (clock), mutation `immutable < appendOnly < monotonic <
readWrite` is the FIRST proper total-order chain.  Its distinct content is `mutationIsTotalOrder` (every pair
comparable — NO antichain, the structural opposite of overflow/clock); the covering chain + four-distinct
witness a genuine four-element chain; `mutationClockProductIsLawful` composes the proper chain with the
infinite-antichain clock (two opposite order shapes) via the shipped `productIsLawful`.  All finite-enum
`cases <;> rfl` (the total order via `first | Or.inl rfl | Or.inr rfl`), propext-free. -/

#assert_no_axioms FX1Poly.Modal.MutationGrade.join
#assert_no_axioms FX1Poly.Modal.mutationLattice
#assert_no_axioms FX1Poly.Modal.mutationIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.mutationIsTotalOrder
#assert_no_axioms FX1Poly.Modal.mutationImmutableBelowAppendOnly
#assert_no_axioms FX1Poly.Modal.mutationAppendOnlyBelowMonotonic
#assert_no_axioms FX1Poly.Modal.mutationMonotonicBelowReadWrite
#assert_no_axioms FX1Poly.Modal.mutationChainHasFourDistinct
#assert_no_axioms FX1Poly.Modal.mutationImmutableIsLeast
#assert_no_axioms FX1Poly.Modal.mutationReadWriteIsGreatest
#assert_no_axioms FX1Poly.Modal.mutationClockProductIsLawful

/-! ## The PREORDER structural class + §6.3 Dim 7 lifetime (`PreorderDimension`) — the THIRD dimension shape

After the ordered semirings (HasGradeOver) and the bounded join-semilattices (all antisymmetric partial
orders), the preorder is the third structural class FX dimensions take: order-only (le_refl + le_trans), NOT
necessarily antisymmetric.  `PreorderDimension` + the induced equivalence KERNEL (equiv_refl/symm/trans = the
kernel is an equivalence relation) + IsAntisymmetric + product.  `boundedJoinSemilatticeToPreorder` +
`latticePreorderIsAntisymmetric` show every lattice forgets to a PARTIAL order (antisymmetric); the §6.3 Dim7
LIFETIME instance (regions ordered by outlives, static outlives all) is the FIRST dimension that is NOT a
partial order — `lifetimeRegionsEquivalentButDistinct` (distinct equal-extent regions mutually outlive) ⟹
`lifetimeIsNotAntisymmetric`.  Completes FX's dimension structural taxonomy.  All term-proofs over
le_refl/le_trans/le_antisymm + Nat.le_refl/le_trans + injection/noConfusion, propext-free. -/

#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_refl
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_symm
#assert_no_axioms FX1Poly.Modal.PreorderDimension.equiv_trans
#assert_no_axioms FX1Poly.Modal.PreorderDimension.IsAntisymmetric
#assert_no_axioms FX1Poly.Modal.PreorderDimension.product
#assert_no_axioms FX1Poly.Modal.boundedJoinSemilatticeToPreorder
#assert_no_axioms FX1Poly.Modal.latticePreorderIsAntisymmetric
#assert_no_axioms FX1Poly.Modal.effectInducedPreorderIsAntisymmetric
#assert_no_axioms FX1Poly.Modal.LifetimeGrade.outlives
#assert_no_axioms FX1Poly.Modal.lifetimeOutlivesRefl
#assert_no_axioms FX1Poly.Modal.lifetimeOutlivesTrans
#assert_no_axioms FX1Poly.Modal.lifetimePreorder
#assert_no_axioms FX1Poly.Modal.lifetimeStaticOutlivesAll
#assert_no_axioms FX1Poly.Modal.lifetimeRegionsEquivalentButDistinct
#assert_no_axioms FX1Poly.Modal.lifetimeIsNotAntisymmetric
#assert_no_axioms FX1Poly.Modal.lifetimeProductPreorder

/-! ## The FIRST cross-dimension comparison (`DimensionRepetitionContrast`) — usage vs security on repetition

The DIM track built each dimension's algebra in isolation; this is the first theorem CONTRASTING two
dimensions' check behaviors.  At the unit `R.one` (`semiringUnits_eq`: usage one = `.one`, security one =
`.classified`), usage `+` is NON-idempotent (`usageAddUnitUnit_eq_omega`: `1+1 = ω ≠ 1` — occurrence
counting, repetition PENALIZED, so `usageRepetitionExceedsLinear`: `ω ≰ 1`) while security `+` IS idempotent
(`securityAddUnitUnit_idempotent`: `classified+classified = classified` — flow join, repetition NOT
penalized, so `securityRepetitionStaysWithinUnit`: `classified ≤ classified`).  usageAndSecurityDifferOn
Repetition: the SAME combine-with-itself operation exceeds the usage bound but stays within the security
bound — composing pointwise in one grade vector (§6.1), each dimension enforces its own discipline
(linearity vs information flow), the algebraic root of §6.8's "the dimensions are NOT orthogonal".  All rfl
over the propext-free enum tables UsageGrade/SecurityGrade .add/.le. -/

#assert_no_axioms FX1Poly.Modal.semiringUnits_eq
#assert_no_axioms FX1Poly.Modal.usageAddUnitUnit_eq_omega
#assert_no_axioms FX1Poly.Modal.usageRepetitionExceedsLinear
#assert_no_axioms FX1Poly.Modal.securityAddUnitUnit_idempotent
#assert_no_axioms FX1Poly.Modal.securityRepetitionStaysWithinUnit
#assert_no_axioms FX1Poly.Modal.usageAndSecurityDifferOnRepetition

/-! ## The MULTIPLICATIVE cross-dimension contrast (`DimensionMultiplicationContrast`) — usage vs security
on the `(R, ×, 1)` monoid + where its unit sits in the order

The multiplicative sibling of `DimensionRepetitionContrast` (which contrasted `+`).  The two dimensions'
MULTIPLICATIVE units sit at OPPOSITE order positions: usage's `×`-unit `1` is SUB-MAXIMAL
(`usageUnitIsSubMaximal`: `1 ≤ ω ∧ 1 ≠ ω` — unrestricted use strictly exceeds linear, usage GRANTS a
beyond-unit `@[copy]` capability) while security's `×`-unit `classified` is MAXIMAL
(`securityUnitIsMaximal`: `classified ≰ unclassified`, `unclassified ≤ classified` — the top secrecy, no
"beyond classified").  The `×`-annihilator (= additive `0`, the universal semiring law `r × 0 = 0`)
differs in MEANING: usage's `0` is erased/ghost (`usageMulAnnihilatesAtZero`: `0 × ω = 0`, the §1.5
erasure / §6.2 `1/ω = 0` context division) while security's `0` is `unclassified`/public
(`securityMulAnnihilatesAtUnclassified`: `classified × unclassified = unclassified` — "ghost computation
on a secret leaks nothing", §6.3 dim 5).  usageAndSecurityDifferOnUnitMaximality: composing pointwise in
one grade vector (§6.1), each dimension's `(R, ×, 1)` relates to its order differently — usage's unit
admits a strict over-grade, security's does not — so the 21-dim product is heterogeneous on `×`/`≤` too
(§6.8).  All rfl/decide over the propext-free enum tables UsageGrade/SecurityGrade .mul/.le. -/

#assert_no_axioms FX1Poly.Modal.usageUnitIsSubMaximal
#assert_no_axioms FX1Poly.Modal.securityUnitIsMaximal
#assert_no_axioms FX1Poly.Modal.usageMulAnnihilatesAtZero
#assert_no_axioms FX1Poly.Modal.securityMulAnnihilatesAtUnclassified
#assert_no_axioms FX1Poly.Modal.usageAndSecurityDifferOnUnitMaximality

/-! ## The chain-vs-diamond DISTRIBUTIVITY dichotomy (`LatticeDistributivityClassification`)

The structural capstone of the lattice-family work: classify FX's bounded-lattice dimensions by distributivity,
the deepest lattice-theoretic invariant.  MutationGrade.meet (the chain MIN, dual to the shipped chain-max join)
+ meet-semilattice laws (comm/assoc/idempotent) + the two absorption laws (mutationJoinMeetAbsorb /
mutationMeetJoinAbsorb) establish the mutation 4-chain is a genuine bounded LATTICE.  mutationIsDistributive: the
4-chain satisfies `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)` (chains are always distributive; min distributes over max,
64-leaf cases<;>rfl — a non-trivial chain, not a 2-element triviality).  ★ mutationChainDistributesButOverflow
DiamondDoesNot: the dichotomy — mutation distributes but the overflow diamond M3 does NOT (citing the shipped
overflowIsNonDistributive).  Among FX's lattice dimensions, distributivity tracks the order shape exactly: the
chains are distributive, only the antichain-bearing diamond M3 is non-distributive — §6.8 heterogeneity at the
deepest lattice level.  All zero-axiom (cases<;>rfl + the shipped overflowIsNonDistributive). -/

#assert_no_axioms FX1Poly.Modal.MutationGrade.meet
#assert_no_axioms FX1Poly.Modal.mutationMeet_comm
#assert_no_axioms FX1Poly.Modal.mutationMeet_assoc
#assert_no_axioms FX1Poly.Modal.mutationMeet_idempotent
#assert_no_axioms FX1Poly.Modal.mutationJoinMeetAbsorb
#assert_no_axioms FX1Poly.Modal.mutationMeetJoinAbsorb
#assert_no_axioms FX1Poly.Modal.mutationIsDistributive
#assert_no_axioms FX1Poly.Modal.mutationChainDistributesButOverflowDiamondDoesNot

/-! ## The session-type dimension (§6.3 Dim 6 / §11) — the first INVOLUTION-structured dimension
(`SessionDualityDimension`)

Every prior dimension is an order/algebra (semiring / lattice / PCM / preorder); the PROTOCOL dimension is
structurally different — its defining operation is DUALITY, an INVOLUTION (the protocol of the opposite
endpoint), not a binary combine.  SessionType (5-ctor: endSession / send / receive / selectChoice / branchOffer)
+ SessionType.dual (§11.2: send↔receive, select↔branch, end self-dual, payload-agnostic) + the 5 per-ctor duality
equations (rfl). ★ SessionType.dual_involutive: dual(dual S)=S (the headline — the structural signature of Dim 6;
a channel's two endpoints are mutually dual, §11.2). SessionType.dual_injective: duality is INJECTIVE hence a
BIJECTION on the protocol space (involution ⟹ bijective). selfDual_iff_endSession: endSession is the UNIQUE
self-dual protocol (any communicating protocol's head ctor flips under duality, so it has a DISTINCT dual). ★
sessionDualityIsInvolutionButNotIdentity: an involution but NOT the identity (a send is not its own dual) — the
genuine reversal distinguishing this dimension from the order/algebra ones. Complements L1-SESSION (#959, the
§27.2 linearity-mechanism witness) with the session-type ALGEBRA. All zero-axiom (plain-inductive recursor +
rfl + congrArg + noConfusion + decide). -/

#assert_no_axioms FX1Poly.Modal.SessionType
#assert_no_axioms FX1Poly.Modal.SessionType.dual
#assert_no_axioms FX1Poly.Modal.dual_endSession
#assert_no_axioms FX1Poly.Modal.dual_send
#assert_no_axioms FX1Poly.Modal.dual_receive
#assert_no_axioms FX1Poly.Modal.dual_selectChoice
#assert_no_axioms FX1Poly.Modal.dual_branchOffer
#assert_no_axioms FX1Poly.Modal.SessionType.dual_involutive
#assert_no_axioms FX1Poly.Modal.SessionType.dual_injective
#assert_no_axioms FX1Poly.Modal.selfDual_iff_endSession
#assert_no_axioms FX1Poly.Modal.sessionDualityIsInvolutionButNotIdentity

/-! ## Session-type OPERATIONAL semantics (§11.3 / §11.11) — communication preserves duality + no deadlock
(`SessionCommunication`)

The dynamics over the duality algebra. CommStep (6-arm: matched send/receive exchange + select/branch resolution
left/right + the mirror) is one synchronized communication on a PAIR of endpoints (a channel = a dual pair,
§11.2). ★ CommStep.preservesDuality: session FIDELITY — a DUAL pair steps to a DUAL pair (the core safety:
well-formed channels never reach a mismatched state; the dual hypothesis forces matched continuations, by cases +
injection auto-subst). dualPairProgresses: a non-end dual channel can always step. dualChannelProgressesOrIsDone:
the PROGRESS dichotomy — a dual channel either steps or IS the terminal (end,end), so no stuck states except
completion (§11.11 deadlock-freedom for a single channel). endChannelIsTerminal: (end,end) has no step.
concreteChannelStep: non-vacuity (send 0.end / receive 0.end actually exchanges). Builds on firing-82's
SessionDualityDimension; complements L1-SESSION (#959). All zero-axiom (inductive Prop relation + cases +
injection + noConfusion). -/

#assert_no_axioms FX1Poly.Modal.CommStep
#assert_no_axioms FX1Poly.Modal.CommStep.preservesDuality
#assert_no_axioms FX1Poly.Modal.dualPairProgresses
#assert_no_axioms FX1Poly.Modal.dualChannelProgressesOrIsDone
#assert_no_axioms FX1Poly.Modal.endChannelIsTerminal
#assert_no_axioms FX1Poly.Modal.concreteChannelStep
-- WHY DUALITY IS NECESSARY (SessionCommunication, §27.2-flavored necessity completing the session arc): the
-- complement of dualChannelProgressesOrIsDone — drop the duality hypothesis and deadlock returns. A mismatched
-- send/send channel (send 0.end, send 0.end) is STUCK (sendSendStuck — no CommStep arm matches two senders) yet
-- not terminal, and exactly NON-dual (sendSendIsNotDual). nonDualChannelDeadlocks: ∃ a non-dual stuck non-terminal
-- config. dualPartnerFixesTheMismatchedDeadlock: the SAME first endpoint deadlocks with a mismatched partner but
-- COMMUNICATES with its dual partner (via concreteChannelStep) — duality IS the fix. ★ dualityIsNecessaryForDead
-- lockFreedom: dual channels never deadlock but a non-dual one can, so the duality hypothesis is ESSENTIAL (the
-- session analogue of SN-NECESSITY #950: the discipline rules out the bad behavior). Caps the session arc (82
-- algebra / 83 safety / 84 necessity). All zero-axiom (cases-impossibility + decide + cite).
#assert_no_axioms FX1Poly.Modal.sendSendStuck
#assert_no_axioms FX1Poly.Modal.sendSendIsNotDual
#assert_no_axioms FX1Poly.Modal.nonDualChannelDeadlocks
#assert_no_axioms FX1Poly.Modal.dualPartnerFixesTheMismatchedDeadlock
#assert_no_axioms FX1Poly.Modal.dualityIsNecessaryForDeadlockFreedom

/-! ## §6.3 Dim 8 / §1.1 provenance dimension — the FIRST INFINITE FULL LATTICE M_omega
(`ProvenanceLatticeDimension`)

Combines the two prior lattice advances: clock shipped the INFINITE carrier (but join-only); overflow shipped
the FULL lattice (but a FINITE M3).  Provenance `{opaqueOrigin (bottom), source (originId : Nat), unknown (top)}`
is the first lattice BOTH infinite AND full — the kernel's first concrete M_omega (infinitely many origin atoms,
all joining to `unknown` and meeting to `opaqueOrigin`).  The `source`-`source` join/meet laws reuse the clock
`Nat.beq` facts; the meet (`provenanceMeet_comm`/`_assoc`) + absorption (`provenanceJoinMeetAbsorb`/`provenance
MeetJoinAbsorb`) upgrade the join-semilattice to a full lattice; `provenanceIsNonDistributive` is the concrete
M3-sublattice failure (M_omega contains M3).  The GENUINELY-NEW SEMANTIC content: unlike clock's `crossDomain
Error` (a type error), provenance's `unknown` is a LEGITIMATE value a sink rejects — `isKnownSource` accepts
`source _`, rejects `unknown`/`opaqueOrigin`, and `provenanceKnownSourceLostOnDistinctMerge` shows the
known-origin property is LOST when two distinct origins merge (the §25.5 supply-chain guarantee).  `provenance
ClockProductIsLawful` is the FIRST composition of TWO infinite-antichain dimensions.  All propext-free; general
symbolic modularity deferred (the concrete non-distributivity pins it as genuinely non-distributive). -/

#assert_no_axioms FX1Poly.Modal.ProvenanceGrade.join
#assert_no_axioms FX1Poly.Modal.ProvenanceGrade.meet
#assert_no_axioms FX1Poly.Modal.provenanceJoinSourceWithSelf
#assert_no_axioms FX1Poly.Modal.provenanceLattice
#assert_no_axioms FX1Poly.Modal.provenanceJoinCommutes
#assert_no_axioms FX1Poly.Modal.provenanceJoinAssociates
#assert_no_axioms FX1Poly.Modal.provenanceIsLawfulBoundedJoinSemilattice
#assert_no_axioms FX1Poly.Modal.provenanceSourceIncomparableOfDistinct
#assert_no_axioms FX1Poly.Modal.provenanceSource01Incomparable
#assert_no_axioms FX1Poly.Modal.provenanceOpaqueIsLeast
#assert_no_axioms FX1Poly.Modal.provenanceUnknownIsGreatest
#assert_no_axioms FX1Poly.Modal.provenanceMeetSourceWithSelf
#assert_no_axioms FX1Poly.Modal.provenanceMeet_comm
#assert_no_axioms FX1Poly.Modal.provenanceMeet_assoc
#assert_no_axioms FX1Poly.Modal.provenanceJoinMeetAbsorb
#assert_no_axioms FX1Poly.Modal.provenanceMeetJoinAbsorb
#assert_no_axioms FX1Poly.Modal.provenanceMeetDistinctIsOpaque
#assert_no_axioms FX1Poly.Modal.provenanceIsNonDistributive
#assert_no_axioms FX1Poly.Modal.ProvenanceGrade.isKnownSource
#assert_no_axioms FX1Poly.Modal.provenanceKnownSourceAccepts
#assert_no_axioms FX1Poly.Modal.provenanceUnknownRejected
#assert_no_axioms FX1Poly.Modal.provenanceOpaqueRejected
#assert_no_axioms FX1Poly.Modal.provenanceJoinDistinctSourcesIsUnknown
#assert_no_axioms FX1Poly.Modal.provenanceKnownSourceLostOnDistinctMerge
#assert_no_axioms FX1Poly.Modal.provenanceClockProductLattice
#assert_no_axioms FX1Poly.Modal.provenanceClockProductIsLawful

/-! ### Self-application untypability — the occurs-check that excludes `Ω` from the typed calculus

`λx. x x` has no `HasGradeOver R` derivation in any graded dimension: self-application would force the
binder type `D = (D -> codomain)`, impossible for the finite `GTypeOver R`.  This is the metatheoretic
reason the typed graded calculus is SN despite `Ω` diverging untyped (#950/#960) — the SR-breaking term
is excluded at the typing layer.  Generic over `R`, instantiated at usage + security. -/

#assert_no_axioms FX1Poly.Modal.gTypeOver_ne_self_arrow
#assert_no_axioms FX1Poly.Modal.selfApplicationLambda_untypableOver
#assert_no_axioms FX1Poly.Modal.omegaCombinator_untypableOver
#assert_no_axioms FX1Poly.Modal.usageSelfApp_untypable
#assert_no_axioms FX1Poly.Modal.securitySelfApp_untypable

/-! ### Progress / canonical forms — the second half of type safety for the graded engine

A closed well-typed `HasGradeOver R` term is never stuck: it β-reduces or is a `.lam` value
(`closedWellTypedProgress`), the structural core being canonical forms (a closed normal form is a
`.lam`, `closedNormalFormIsLam`).  With β SR (preservation, #905/#906) and SN (#878) this completes the
safety kit; base type has no closed values (`closedBaseTypeAlwaysSteps`).  Generic over every graded
dimension. -/

#assert_no_axioms FX1Poly.Modal.closedNormalFormIsLam
#assert_no_axioms FX1Poly.Modal.closedWellTypedProgress
#assert_no_axioms FX1Poly.Modal.closedBaseTypeAlwaysSteps
#assert_no_axioms FX1Poly.Modal.usageLinearIdentity_isValue

/-! ### Full-β subject reduction + evaluation — the graded type-safety capstone

Lifts SR from root-β to the FULL congruence-closed β-reduction (`hasGradeOver_reducesPreservation`,
grades exact) + its `ReducesStar` closure, and combines preservation + progress + SN into EVALUATION:
every closed well-typed term β-reduces to a `.lam` value (`closedReducesToLam`).  Well-typed graded
programs evaluate — generic over every dimension. -/

#assert_no_axioms FX1Poly.Modal.hasGradeOver_reducesPreservation
#assert_no_axioms FX1Poly.Modal.hasGradeOver_reducesStarPreservation
#assert_no_axioms FX1Poly.Modal.closedReducesToLam
#assert_no_axioms FX1Poly.Modal.usageLinearIdentity_reducesToLam

/-! ### Logical consistency — the Curry-Howard conclusion of the graded type-safety story

Reading `GTypeOver R` as a proposition and `HasGradeOver R [] _ term T` as a closed proof of `T`, the
graded calculus is CONSISTENT: its atomic proposition `GTypeOver.base` has no closed proof
(`closedBaseTypeUninhabited`), over EVERY dimension `R` at once.  A closed base-typed term would
evaluate to a `.lam` (`closedReducesToLam`), which stays base-typed by SR-over-↝* yet a `.lam` is only
arrow-typed (`invertLam`) — a constructor clash.  `closedTermIsArrowTyped` is the positive reading
(every closed inhabitant is a function); `usageBaseTypeUninhabited` instantiates at the linear
`{0,1,ω}` semiring.  The graded analogue of the grown SN-050 `EmptyType` consistency — atom vs
dedicated empty type. -/

#assert_no_axioms FX1Poly.Modal.closedBaseTypeUninhabited
#assert_no_axioms FX1Poly.Modal.closedTermIsArrowTyped
#assert_no_axioms FX1Poly.Modal.usageBaseTypeUninhabited

/-! ### Version dimension — the first CATEGORY-structured dimension (§6.3 Tier V / §15)

Version labels + total migration adapters form a genuine category: composition + identity + the
category laws (`Migration.compose_assoc`/`identity_compose`/`compose_identity`), `refines` as the induced
reachability preorder, the §14.1 UserApi v1→v2→v3 chain, the §14.2 add/remove retraction pair, and
non-thin hom-sets (proof-relevant adapters).  The first dimension whose grades carry composable morphism
DATA, not a bare order. -/

#assert_no_axioms FX1Poly.Modal.Migration.identity
#assert_no_axioms FX1Poly.Modal.Migration.compose
#assert_no_axioms FX1Poly.Modal.Migration.identity_compose
#assert_no_axioms FX1Poly.Modal.Migration.compose_identity
#assert_no_axioms FX1Poly.Modal.Migration.compose_assoc
#assert_no_axioms FX1Poly.Modal.migrateAddField
#assert_no_axioms FX1Poly.Modal.migrateUserV1toV3_apply
#assert_no_axioms FX1Poly.Modal.Refines.refl
#assert_no_axioms FX1Poly.Modal.Refines.trans
#assert_no_axioms FX1Poly.Modal.userApiV3_refines_v1
#assert_no_axioms FX1Poly.Modal.migrateDropField_addField
#assert_no_axioms FX1Poly.Modal.migrateAddField_injective_inDefault

/-! ### The verified normalizer evaluates well-typed terms to values

`GradedLambda.normalize` computes a `.lam` value for every closed well-typed term
(`closedNormalizesToLam`) — the executable payoff of progress + full-β SR + SN; plus typed evaluation
determinism (`closedConvertibleSameValue`) and the usage/security orthogonal-composition smokes. -/

#assert_no_axioms FX1Poly.Modal.closedNormalizesToLam
#assert_no_axioms FX1Poly.Modal.closedConvertibleSameValue
#assert_no_axioms FX1Poly.Modal.usageClosedNormalizesToLam
#assert_no_axioms FX1Poly.Modal.securityClosedNormalizesToLam

/-! ## PrecisionOverflowCollision — the FIRST §6.8 CROSS-DIMENSION soundness collision (`decimal × overflow(wrap)`)

§6.8 (the "dimensions are NOT orthogonal" catalog, distinct from the §27.2 known-unsoundness corpus) lists
`decimal × overflow(wrap)` among the cross-dimension collisions.  Built on the shipped `OverflowGrade`:
`PrecisionGrade {exact,inexact}` + `OverflowGrade.isExactnessPreserving` (exact/trap true; wrap/saturate/conflict
false) + `forcedPrecision` (dual view, coherent via `forcedPrecision_exactPrecision_iff_isExactnessPreserving`).
`IsJointlyConsistent precision overflow := precision = exact → overflow.isExactnessPreserving`.  THE COLLISION:
`exactPrecisionCollidesWithWrapOverflow` (★) — exact precision (decimal) and wrap overflow are NOT jointly
consistent (wrap silently yields a `mod 2^n` value ≠ the true result); + the `saturate` twin.  SPECIFIC, not
blanket: exact precision composes with the exactness-preserving modes (exact/trap), inexact precision with every
mode.  FULL characterization: `exactPrecisionCollision_iff_notPreserving` (collision set = exactly the
non-preserving modes) + `isJointlyConsistent_iff` (consistent ↔ inexact ∨ preserving).  The §6.8 thesis made
concrete: precision and overflow cannot be chosen independently.  All zero-axiom (Bool.noConfusion /
PrecisionGrade.noConfusion / cases-rfl, no propext). -/

#assert_no_axioms FX1Poly.Modal.OverflowGrade.isExactnessPreserving
#assert_no_axioms FX1Poly.Modal.OverflowGrade.forcedPrecision
#assert_no_axioms FX1Poly.Modal.forcedPrecision_exactPrecision_iff_isExactnessPreserving
#assert_no_axioms FX1Poly.Modal.exactPrecisionCollidesWithWrapOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionCollidesWithSaturateOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionConsistentWithExactOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionConsistentWithTrapOverflow
#assert_no_axioms FX1Poly.Modal.inexactPrecisionConsistentWithEveryOverflow
#assert_no_axioms FX1Poly.Modal.exactPrecisionCollision_iff_notPreserving
#assert_no_axioms FX1Poly.Modal.isJointlyConsistent_iff

/-! ## SoundnessCollisionSchema — the §6.8 collision FORM abstracted; two collisions as ONE schema

The §6.8 catalog is instances of one pattern: a strong GUARANTEE-demand meeting a CAPABILITY that fails to
preserve the invariant.  SoundnessCollisionSchema (Demand/Capability/isStrongDemand/preservesInvariant) +
IsConsistent (strongDemand ⟹ preserved) + the generic notConsistent_iff (collision ⟺ strong ∧ ¬preserving) /
consistent_iff, proved once via Bool helpers notImplies_iff/implies_iff.  INSTANCE 1 decimalOverflowSchema
RECOVERS #1021 (decimalOverflowSchema_recovers_collision) and decimalOverflowSchema_consistent_iff_jointly
Consistent proves the schema SUBSUMES the bespoke IsJointlyConsistent (via isExact_eq_true_iff).  INSTANCE 2 (NEW)
monotonicConcurrentSchema over the shipped MutationGrade chain: concurrentCollidesWithMonotonic (★) — monotonic
mutation is unsound under unsynchronized concurrent access (out-of-order commits break the forward-only
invariant) + appendOnly/readWrite twins (all need sequencing); concurrentConsistentWithImmutable (read-only safe);
sequentialConsistentWithEveryMutation (no demand → no collision).  PAYOFF: two §6.8 collisions across four
dimensions (precision/overflow/mutation/concurrency) are the SAME theorem twice.  All zero-axiom (cases-Bool +
noConfusion + (notConsistent_iff _ _).mpr ⟨rfl,rfl⟩). -/

#assert_no_axioms FX1Poly.Modal.notImplies_iff
#assert_no_axioms FX1Poly.Modal.implies_iff
#assert_no_axioms FX1Poly.Modal.SoundnessCollisionSchema.IsConsistent
#assert_no_axioms FX1Poly.Modal.SoundnessCollisionSchema.notConsistent_iff
#assert_no_axioms FX1Poly.Modal.SoundnessCollisionSchema.consistent_iff
#assert_no_axioms FX1Poly.Modal.PrecisionGrade.isExact
#assert_no_axioms FX1Poly.Modal.decimalOverflowSchema
#assert_no_axioms FX1Poly.Modal.decimalOverflowSchema_recovers_collision
#assert_no_axioms FX1Poly.Modal.isExact_eq_true_iff
#assert_no_axioms FX1Poly.Modal.decimalOverflowSchema_consistent_iff_jointlyConsistent
#assert_no_axioms FX1Poly.Modal.ConcurrencyGrade.isConcurrent
#assert_no_axioms FX1Poly.Modal.MutationGrade.isConcurrencySafe
#assert_no_axioms FX1Poly.Modal.monotonicConcurrentSchema
#assert_no_axioms FX1Poly.Modal.concurrentCollidesWithMonotonic
#assert_no_axioms FX1Poly.Modal.concurrentCollidesWithAppendOnly
#assert_no_axioms FX1Poly.Modal.concurrentCollidesWithReadWrite
#assert_no_axioms FX1Poly.Modal.concurrentConsistentWithImmutable
#assert_no_axioms FX1Poly.Modal.sequentialConsistentWithEveryMutation

/-! ## ThreeWayCollisionClassifiedAsyncSession — §6.8's genuinely THREE-WAY collision (irreducible to any pair)

§6.8's catalog is eight TWO-WAY collisions (each a single dimension pair, captured by SoundnessCollisionSchema
#1022) PLUS one genuinely THREE-WAY collision: classified × async × session (a classified value's ordering leaks
through async session interleaving). IsClassifiedAsyncSessionAdmissible (c a s : Bool) := ¬(c ∧ a ∧ s). ★
classifiedAsyncSessionCollision: ¬admissible(true,true,true). The HEADLINE structural fact —
classifiedAsyncSessionIrreducible: each PAIR (third capability withheld) IS admissible (true,true,false /
true,false,true / false,true,true), so NO proper subset collides — the collision is genuinely 3-way, unlike the
2-way #1021/#1022 which collide on a single pair (no SoundnessCollisionSchema over any pair captures it).
isAdmissible_iff: admissible ↔ ≥1 capability withheld (De Morgan, cases + Bool.noConfusion). Spans §6.8
structurally: 2-way reducible + this 3-way irreducible. All zero-axiom. -/

#assert_no_axioms FX1Poly.Modal.IsClassifiedAsyncSessionAdmissible
#assert_no_axioms FX1Poly.Modal.classifiedAsyncSessionCollision
#assert_no_axioms FX1Poly.Modal.classifiedAsync_admissibleWithoutSession
#assert_no_axioms FX1Poly.Modal.classifiedSession_admissibleWithoutAsync
#assert_no_axioms FX1Poly.Modal.asyncSession_admissibleWithoutClassified
#assert_no_axioms FX1Poly.Modal.classifiedAsyncSessionIrreducible
#assert_no_axioms FX1Poly.Modal.isAdmissible_iff

/-! ### §1.3 flagship `encrypt_and_send` — jointly §6.8-admissible multi-dimension grade configuration
    (#1027 DIM-FLAGSHIP, FlagshipMultiDimensionSignature.lean)

The POSITIVE counterpart to the §6.8 collision corpus: a real multi-dimension signature lands in the
admissible region across every relevant collision at once. IsImplicitFlowAdmissible REFINES #1026's
co-occurrence 3-way collision per §12.2 (the collision fires only when the classified value CONTROLS
the async session scheduling, not when it merely co-occurs): encryptAndSendImplicitFlowAdmissible
admits the flagship (secret flows to CT encryption, not scheduling); secretControlsSchedulingCollision
keeps the genuine attack rejected; implicitFlowAdmissible_ofCoOccurrenceAdmissible = soundness of the
refinement; flagshipDistinguishesModels = it is strictly more permissive on the flagship itself.
encryptAndSendGradeMonoidIsLawful = the concrete usage×security×effect 3-factor grade vector is lawful
(free from productIsLawful); encryptAndSendJointlyAdmissible (★) = the signature satisfies the 3-way
implicit-flow + monotonic×concurrent + decimal×overflow constraints SIMULTANEOUSLY. All zero-axiom
(Bool.noConfusion / structure projections / shipped productIsLawful + sequentialConsistentWithEvery-
Mutation). -/

#assert_no_axioms FX1Poly.Modal.IsImplicitFlowAdmissible
#assert_no_axioms FX1Poly.Modal.encryptAndSendImplicitFlowAdmissible
#assert_no_axioms FX1Poly.Modal.secretControlsSchedulingCollision
#assert_no_axioms FX1Poly.Modal.implicitFlowAdmissible_ofCoOccurrenceAdmissible
#assert_no_axioms FX1Poly.Modal.flagshipDistinguishesModels
#assert_no_axioms FX1Poly.Modal.encryptAndSendGradeMonoidIsLawful
#assert_no_axioms FX1Poly.Modal.encryptAndSendKeyGrade_combine_identity
#assert_no_axioms FX1Poly.Modal.encryptAndSendMutationConcurrencyConsistent
#assert_no_axioms FX1Poly.Modal.encryptAndSendPrecisionOverflowConsistent
#assert_no_axioms FX1Poly.Modal.encryptAndSendJointlyAdmissible

/-! ### §6.8 collision catalog — completed + classified into co-occurrence vs scoping-refined
    (#1028 DIM-COLLISION-CATALOG, SoundnessCollisionCatalog.lean)

Generalizes #1027's implicit-flow insight into a whole structural CLASS. ghost×runtime = the clean
CO-OCCURRENCE entry (ghostObservedAtRuntimeCollision = grade-0 observed at runtime collides
unconditionally; runtimePresentValueObservable + unobservedGhostConsistent pin the specificity).
borrow×Async + borrow×unscoped-spawn = SCOPING-REFINED (the demand is the ESCAPE control, not presence):
borrowEscapeUnderAsyncCollision / borrowEscapeIntoUnscopedSpawnCollision collide, but confinedBorrowUnder
AsyncConsistent / borrowIntoScopedSpawnConsistent show a CONFINED borrow co-occurs soundly (= why
encrypt_and_send borrows under async, #1027). ★ catalogHasTwoCollisionClasses = the structural dichotomy
(co-occurrence collides on joint presence; scoping-refined is consistent on joint presence + respected
scope). All SoundnessCollisionSchema instances, zero-axiom (notConsistent_iff.mpr ⟨rfl,rfl⟩ /
Bool.noConfusion / fun _ => rfl). -/

#assert_no_axioms FX1Poly.Modal.ghostObservedAtRuntimeCollision
#assert_no_axioms FX1Poly.Modal.runtimePresentValueObservable
#assert_no_axioms FX1Poly.Modal.unobservedGhostConsistent
#assert_no_axioms FX1Poly.Modal.borrowEscapeUnderAsyncCollision
#assert_no_axioms FX1Poly.Modal.confinedBorrowUnderAsyncConsistent
#assert_no_axioms FX1Poly.Modal.borrowEscapeIntoUnscopedSpawnCollision
#assert_no_axioms FX1Poly.Modal.borrowIntoScopedSpawnConsistent
#assert_no_axioms FX1Poly.Modal.catalogHasTwoCollisionClasses

/-! ### §6.8 collision catalog COMPLETE — the last 3 entries (#1032 DIM-COLLISION-CATALOG-COMPLETE,
    SoundnessCollisionCatalogComplete.lean)

The final three §6.8 entries, all control-refined: CT×Async (constantTimeCollidesWithSecretDependentAsync +
constantTimeConsistentWithSecretIndependentAsync + variableTimeConsistentWithAnyAsync), classified×Fail
(secretControlledFailureCollidesWithObservableFailure + secretControlledFailureConsistentWithClassifiedFailure +
secretIndependentFailureConsistentWithAnyObservability), CT×Fail-on-secret (constantTimeCollidesWithSecret
DependentFailure + constantTimeConsistentWithSecretIndependentFailure). ★ sec68RemainingCatalogControlRefined =
all three co-occur soundly when the control is withheld. Completes the entire 9-entry §6.8 catalog (3 co-occurrence
+ 6 control-refined). All SoundnessCollisionSchema instances, zero-axiom (notConsistent_iff.mpr ⟨rfl,rfl⟩ /
Bool.noConfusion / fun _ => rfl). -/

#assert_no_axioms FX1Poly.Modal.constantTimeCollidesWithSecretDependentAsync
#assert_no_axioms FX1Poly.Modal.constantTimeConsistentWithSecretIndependentAsync
#assert_no_axioms FX1Poly.Modal.variableTimeConsistentWithAnyAsync
#assert_no_axioms FX1Poly.Modal.secretControlledFailureCollidesWithObservableFailure
#assert_no_axioms FX1Poly.Modal.secretControlledFailureConsistentWithClassifiedFailure
#assert_no_axioms FX1Poly.Modal.secretIndependentFailureConsistentWithAnyObservability
#assert_no_axioms FX1Poly.Modal.constantTimeCollidesWithSecretDependentFailure
#assert_no_axioms FX1Poly.Modal.constantTimeConsistentWithSecretIndependentFailure
#assert_no_axioms FX1Poly.Modal.sec68RemainingCatalogControlRefined
