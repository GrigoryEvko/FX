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

/-! # FX1PolyAudit/AuditModalGradedJudgment — modal/dimension-layer zero-axiom gates, shard 2 of 4 (split from the AuditModal monolith for parallel gate elaboration) -/

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

