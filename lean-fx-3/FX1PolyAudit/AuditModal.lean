import FX1PolyAudit.DependencyAudit
import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradeVector
import FX1Poly.Modal.GradeVectorGeneric
import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Modal.GradedTyping
import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.GradeErasureGeneric
import FX1Poly.Modal.GradedWeakeningGeneric
import FX1Poly.Modal.GradedTypingMetatheory
import FX1Poly.Modal.GradedSubjectReduction
import FX1Poly.Modal.GradeErasure
import FX1Poly.Modal.SimpleStrongNormalization
import FX1Poly.Modal.GradedSubstitutionAlgebra
import FX1Poly.Modal.GradedReductionSubstitution
import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Modal.GradedComposition
import FX1Poly.Modal.GradedReductionConfluence
import FX1Poly.Modal.GradedNormalization

/-! # FX1PolyAudit/AuditModal — per-declaration zero-axiom gate for the resource-graded doctrine
   (the SECOND graded dimension: Usage `{0, 1, ω}` and Security `{unclassified < classified}`)

`FX1Poly.Modal.ResourceGraded` is the substrate for FX's usage dimension — the first graded
dimension beyond Type (§6.1).  The usage grade algebra `{0, 1, ω}` is proven a genuine ORDERED
SEMIRING (`IsLawfulOrderedGradeSemiring fxUsageSemiring`): commutative-monoid `+`, monoid `*`,
distributivity, annihilation, and a partial order compatible with both operations.

Each gate fails the build if its declaration depends on `propext` / `Quot.sound` / `Classical` /
`sorry` / `native_decide` / `omega`.  This brings the previously-ungated `ResourceGraded` surface
under the same per-declaration discipline as the rest of the kernel.
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

/-! ### Usage core semiring laws (associativity / commutativity / distributivity — DIM2-1) -/

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

/-! ### The verified-semiring bundle + the usage witness (DIM2-1 headline) -/

#assert_no_axioms FX1Poly.Modal.IsLawfulOrderedGradeSemiring
#assert_no_axioms FX1Poly.Modal.fxUsageSemiring_isLawful

/-! ### Security grade-algebra laws + the verified-semiring witness (DIM5-1, the 2nd graded dimension) -/

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

/-! ### Grade-vector substrate (DIM2-2): the per-binding usage grade vector + its semimodule laws -/

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

/-! ### Grade division — the residual of multiplication (toward DIM2-3's corrected Lam rule) -/

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

/-! ### The usage grade check + the Atkey-2018 broken-Lam rejection (DIM2-6 / §27.1 / §27.2) -/

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

/-! ### Generic grade-vector substrate over any OrderedGradeSemiring (DIM5-2 + dims 6–21) -/

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

/-! ### The GENERIC graded typing judgment over any OrderedGradeSemiring (DIM5-3 + dims 6–21)

`HasGradeOver R` — the §6.2 grade-checking judgment (corrected Wood/Atkey Lam + App scaling), generic
over the ordered semiring, on the DIM5-2 generic vector.  Structural metatheory (3 inversions + the
length-coherence invariant) transfers from DIM2-3 verbatim.  The witnesses type the linear identity +
K combinator at BOTH usage and security — the orthogonal-composition thesis at the JUDGMENT layer. -/

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

/-! ### Generic grade erasure + SN-transfer over any OrderedGradeSemiring (DIM5-4 + dims 6–21)

`HasGradeOver R` erases to the SAME grade-free `HasSimpleType` that `HasUsage` erases to, so STLC strong
normalization (the shipped Tait FT) transfers to the generic judgment for ANY dimension R — no
graded-reducibility re-proof.  The generic DIM2-4/DIM2-5; the orthogonal-composition thesis (SN survives
erasure) at the judgment layer for all 21 dimensions at once. -/

#assert_no_axioms FX1Poly.Modal.eraseGTypeOver
#assert_no_axioms FX1Poly.Modal.lookup_map_eraseGTypeOver
#assert_no_axioms FX1Poly.Modal.HasGradeOver.erase
#assert_no_axioms FX1Poly.Modal.HasGradeOver.stronglyNormalizing
#assert_no_axioms FX1Poly.Modal.linearIdentityOver_stronglyNormalizing
#assert_no_axioms FX1Poly.Modal.securityLinearIdentity_stronglyNormalizingViaGeneric
#assert_no_axioms FX1Poly.Modal.securityKCombinator_stronglyNormalizingViaGeneric

/-! ### Generic weakening for HasGradeOver R over any OrderedGradeSemiring (DIM5-5 + dims 6–21)

The de Bruijn weakening metatheory generic over R: `HasGradeOver R` survives `GradedLambda.shift` at
any cut, inserting a `R.zero` grade.  Mirrors DIM2's `GradedTypingMetatheory`; the App-case grade
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

/-! ### The SOUND graded typing judgment (DIM2-3): type-coupled HasUsage with App scaling -/

#assert_no_axioms FX1Poly.Modal.GType
#assert_no_axioms FX1Poly.Modal.GType.lookup
#assert_no_axioms FX1Poly.Modal.HasUsage
#assert_no_axioms FX1Poly.Modal.linearIdentity_typed
#assert_no_axioms FX1Poly.Modal.kCombinator_typed

/-! ### HasUsage structural metatheory (DIM2-3): inversion + length invariant + weakening -/

#assert_no_axioms FX1Poly.Modal.HasUsage.invertVar
#assert_no_axioms FX1Poly.Modal.HasUsage.invertLam
#assert_no_axioms FX1Poly.Modal.HasUsage.invertApp
#assert_no_axioms FX1Poly.Modal.insertTypeAt
#assert_no_axioms FX1Poly.Modal.GradeVector.insertAt
#assert_no_axioms FX1Poly.Modal.length_insertTypeAt
#assert_no_axioms FX1Poly.Modal.lookup_some_lt
#assert_no_axioms FX1Poly.Modal.lookup_insertTypeAt_lt
#assert_no_axioms FX1Poly.Modal.lookup_insertTypeAt_ge
#assert_no_axioms FX1Poly.Modal.insertAt_zero
#assert_no_axioms FX1Poly.Modal.single_insertAt_lt
#assert_no_axioms FX1Poly.Modal.single_insertAt_ge
#assert_no_axioms FX1Poly.Modal.insertAt_scale
#assert_no_axioms FX1Poly.Modal.insertAt_add
#assert_no_axioms FX1Poly.Modal.add_length_eq
#assert_no_axioms FX1Poly.Modal.hasUsage_length
#assert_no_axioms FX1Poly.Modal.hasUsage_weakening

/-! ### β subject reduction (DIM2-3 soundness payoff): graded substitution + β-preservation -/

#assert_no_axioms FX1Poly.Modal.removeTypeAt
#assert_no_axioms FX1Poly.Modal.GradeVector.removeAt
#assert_no_axioms FX1Poly.Modal.GradeVector.gradeAt
#assert_no_axioms FX1Poly.Modal.GradeVector.substInto
#assert_no_axioms FX1Poly.Modal.substInto_succ_cons
#assert_no_axioms FX1Poly.Modal.removeTypeAt_length
#assert_no_axioms FX1Poly.Modal.lookup_removeTypeAt_lt
#assert_no_axioms FX1Poly.Modal.lookup_removeTypeAt_ge
#assert_no_axioms FX1Poly.Modal.gradeAt_nil
#assert_no_axioms FX1Poly.Modal.gradeAt_zero
#assert_no_axioms FX1Poly.Modal.removeAt_zero
#assert_no_axioms FX1Poly.Modal.gradeAt_single_self
#assert_no_axioms FX1Poly.Modal.gradeAt_single_ne
#assert_no_axioms FX1Poly.Modal.removeAt_single_self
#assert_no_axioms FX1Poly.Modal.removeAt_single_lt
#assert_no_axioms FX1Poly.Modal.removeAt_single_gt
#assert_no_axioms FX1Poly.Modal.removeAt_add
#assert_no_axioms FX1Poly.Modal.removeAt_scale
#assert_no_axioms FX1Poly.Modal.gradeAt_scale
#assert_no_axioms FX1Poly.Modal.gradeAt_add
#assert_no_axioms FX1Poly.Modal.add_interchange
#assert_no_axioms FX1Poly.Modal.substInto_single_self
#assert_no_axioms FX1Poly.Modal.substInto_single_lt
#assert_no_axioms FX1Poly.Modal.substInto_single_gt
#assert_no_axioms FX1Poly.Modal.substInto_appGrade
#assert_no_axioms FX1Poly.Modal.hasUsage_substitution
#assert_no_axioms FX1Poly.Modal.hasUsage_betaPreservation

/-! ### Grade erasure (DIM2-4): the usage dimension is a conservative refinement of simple typing -/

#assert_no_axioms FX1Poly.Modal.SimpleType
#assert_no_axioms FX1Poly.Modal.eraseType
#assert_no_axioms FX1Poly.Modal.SimpleType.lookup
#assert_no_axioms FX1Poly.Modal.HasSimpleType
#assert_no_axioms FX1Poly.Modal.lookup_map_eraseType
#assert_no_axioms FX1Poly.Modal.HasUsage.erase
#assert_no_axioms FX1Poly.Modal.linearIdentity_erases

/-! ### STLC strong normalization substrate (DIM2-5): β-reduction + Acc-SN + structural lemmas -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNeutral
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.var
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofAppLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofAppRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofLam
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofReduces

/-! ### Tait reducibility candidates (DIM2-5 ii): Reducible + CR1/CR2/CR3 -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible
#assert_no_axioms FX1Poly.Modal.GradedLambda.reducibilityConditions
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.sn
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.ofReduces
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.ofNeutral
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.var

/-! ### Parallel-substitution σ-algebra (DIM2-5 iii-a): renaming + substitution fusion laws

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

/-! ### Reduction is substitutive (DIM2-5 iii-b): kernel substAt/shift bridge + Reduces.substAt

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

/-! ### Tait SN + the graded-SN transfer (DIM2-5 iii-c / SN-056): the orthogonal-composition payoff

The STLC fundamental theorem (abstraction lemma → fundamental → every well-typed term reducible →
SN) proved ONCE, and the headline `HasUsage.stronglyNormalizing`: graded-SN transfers from
type-dimension SN through grade erasure with no graded-reducibility re-proof.  Concrete non-vacuous
witnesses (linear identity, K combinator). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.lam
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reducible.abstraction
#assert_no_axioms FX1Poly.Modal.ReducibleSubstitution
#assert_no_axioms FX1Poly.Modal.ReducibleSubstitution.cons
#assert_no_axioms FX1Poly.Modal.HasSimpleType.fundamental
#assert_no_axioms FX1Poly.Modal.HasSimpleType.reducible
#assert_no_axioms FX1Poly.Modal.HasSimpleType.stronglyNormalizing
#assert_no_axioms FX1Poly.Modal.HasUsage.stronglyNormalizing
#assert_no_axioms FX1Poly.Modal.linearIdentity_stronglyNormalizing
#assert_no_axioms FX1Poly.Modal.kCombinator_stronglyNormalizing

/-! ### DIM2 composition ledger (DIM2-7): orthogonal composition validated

Graded subject reduction lifted to the full β-reduction, then the metatheory bundle conjoining
type-dimension SN (transferred) with usage-dimension graded-SR on the same reduction — the two
dimensions compose without collision (Usage × Type is a sound pointwise composition, not a §6.8
collision pair).  Concrete grade-preservation β witnesses: `(λx.x) z ↝ z` at scaling `r = 1`, and the
non-trivial `(λx.(g x) x) z ↝ (g z) z` at `r = ω` (the regression test for the `ρ + r·σ` law). -/

#assert_no_axioms FX1Poly.Modal.HasUsage.preservedByReduces
#assert_no_axioms FX1Poly.Modal.HasUsage.metatheoryBundle
#assert_no_axioms FX1Poly.Modal.appliedIdentity
#assert_no_axioms FX1Poly.Modal.appliedIdentity_typed
#assert_no_axioms FX1Poly.Modal.appliedIdentity_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.omegaScalingBinaryType
#assert_no_axioms FX1Poly.Modal.omegaScalingRedex
#assert_no_axioms FX1Poly.Modal.omegaScalingContractum
#assert_no_axioms FX1Poly.Modal.omegaScalingRedex_typed
#assert_no_axioms FX1Poly.Modal.omegaScalingRedex_reductKeepsGrade
#assert_no_axioms FX1Poly.Modal.omegaScalingContractum_typedDirectly

/-! ### β-confluence infrastructure (CONF stage 1): reduction-substitutivity for GradedLambda

Toward completing the substrate into a full reference STLC (SN + SR + confluence → unique NF).
Reduction under renaming/shift (via `Reduces.applySubstitution`), multi-step congruence closures, and
argument-substitutivity — the inputs to the local-confluence critical-pair analysis (next). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_eq_applySubstitution_var
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.shift
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congLam
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.substReducedArg

/-! ### β-confluence (CONF stage 2): local confluence + Newman → confluence on the typed fragment

The 9-case β critical-pair analysis (`WeaklyConfluent Reduces`), then the relation-generic `newmanAux`
(per-term `Acc` = `IsStronglyNormalizing`) gives confluence on the SN fragment — and hence on every
well-(simply/usage-)typed `GradedLambda` term (SN from the Tait FT / grade erasure). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.localConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.weaklyConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.confluent
#assert_no_axioms FX1Poly.Modal.HasSimpleType.confluent
#assert_no_axioms FX1Poly.Modal.HasUsage.confluent

/-! ### Unique normal forms (CONF stage 3a)

Confluence + "a normal form admits no step" ⟹ a strongly-normalizing term has at most one β-NF; hence
every well-(simply/usage-)typed `GradedLambda` term has a unique normal form (the bridge to decidable
conversion). -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm.eq_of_reducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.uniqueNormalForm
#assert_no_axioms FX1Poly.Modal.HasSimpleType.uniqueNormalForm
#assert_no_axioms FX1Poly.Modal.HasUsage.uniqueNormalForm

/-! ### The verified β-normalizer (CONF stage 3b-i)

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

/-! ### Decidable β-conversion (CONF stage 3b-ii — completes the substrate)

Conversion (`Joinable Reduces`) = normal-form equality on the SN fragment, so it is decidable via
`GradedLambda`'s `DecidableEq` on normal forms.  Every well-(simply/usage-)typed term pair has
decidable convertibility — the GradedLambda STLC is now a full reference calculus with decidable
definitional equality. -/

#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofReducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_of_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.joinable_iff_normalize_eq
#assert_no_axioms FX1Poly.Modal.GradedLambda.decidableJoinable
#assert_no_axioms FX1Poly.Modal.HasSimpleType.decidableConv
#assert_no_axioms FX1Poly.Modal.HasUsage.decidableConv
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
#assert_no_axioms FX1Poly.Modal.HasUsage.joinable_trans
