import FX1PolyAudit.DependencyAudit
import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradeVector
import FX1Poly.Modal.GradeVectorGeneric
import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradeErasureGeneric
import FX1Poly.Modal.GradedWeakeningGeneric
import FX1Poly.Modal.GradedSubstitutionGeneric
import FX1Poly.Modal.GradedSubjectReductionGeneric
import FX1Poly.Modal.GradedCompositionGeneric
import FX1Poly.Modal.SimpleStrongNormalization
import FX1Poly.Modal.GradedSubstitutionAlgebra
import FX1Poly.Modal.GradedReductionSubstitution
import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Modal.GradedReductionConfluence
import FX1Poly.Modal.GradedNormalization
import FX1Poly.Modal.ComplexitySemiring
import FX1Poly.Modal.EffectLatticeClassification
import FX1Poly.Modal.UnifiedGradeMonoid

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
