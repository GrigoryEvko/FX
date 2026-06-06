import FX1PolyAudit.DependencyAudit
import FX1Poly.Modal.ResourceGraded
import FX1Poly.Modal.GradeVector
import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Modal.GradedTyping
import FX1Poly.Modal.GradedTypingMetatheory
import FX1Poly.Modal.GradedSubjectReduction
import FX1Poly.Modal.GradeErasure
import FX1Poly.Modal.SimpleStrongNormalization

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
