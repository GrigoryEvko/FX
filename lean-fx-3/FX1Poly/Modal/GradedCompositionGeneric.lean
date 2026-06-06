import FX1Poly.Modal.GradeErasureGeneric
import FX1Poly.Modal.GradedSubjectReductionGeneric

/-! # FX1Poly/Modal/GradedCompositionGeneric — the generic composition ledger (DIM5-8 + dims 6–21)

The capstone of the generic graded-judgment track.  DIM2-7 (`GradedComposition.lean`) validated the
21-dimension composition thesis (§1.1, §6.8) for the USAGE dimension by lifting DIM2-3's root-β subject
reduction to the full β-reduction and bundling both dimensions' metatheory on the same relation.  This
file ships that capstone ONCE, generic over any `OrderedGradeSemiring`, closing the generic reduction
metatheory begun in DIM5-5 (weakening), DIM5-6 (substInto grade-algebra) and DIM5-7 (substitution + β SR).

  * `HasGradeOver.preservedByReduces` — **graded subject reduction over the full β-reduction `Reduces`**:
    a `HasGradeOver R`-typed term keeps its type AND its exact grade vector along every β-step (root-β
    via DIM5-7's `hasGradeOver_betaPreservation`; congruence cases by inversion + grade-preserving
    reassembly), for ANY dimension R.
  * `HasGradeOver.metatheoryBundle` — **the capstone**: a typed term satisfies BOTH dimensions'
    metatheory simultaneously and independently — strong normalization (TYPE dimension, transferred via
    grade erasure, DIM5-4 `stronglyNormalizing`) AND graded subject reduction (the GRADED dimension,
    lifted here) — on the same `Reduces`.  Neither re-proves the other; the two compose without
    collision (a SOUND pointwise composition, not a §6.8 collision pair).
  * `appliedIdentityOver_*` — a concrete β-step `(λx. x) z ↝ z` keeping the EXACT grade
    (`add (z↦0) (scale R.one (z↦R.one))`), proved generically and instantiated at BOTH the security and
    usage dimensions — the App-rule accounting at the trivial scaling `r = R.one`.
  * `usageOmegaScalingRedex_*` — the DECISIVE non-trivial-scaling regression, routed through the GENERIC
    `preservedByReduces` at the usage semiring: `(λx. (g x) x) z ↝ (g z) z` keeps `[z↦ω, g↦1]`.  The
    bound `x` is used twice, so the App rule scales the once-occurring `z`'s usage by `ω`, and `z` is
    correctly tracked at `ω` after β duplicates it.  This `r = ω` case would FAIL if the
    substitution-grade law used `+` (or scale-by-1) instead of the correct `ρ + r · σ` — and here it is
    the GENERIC machinery (not a usage-bespoke proof) that gets it right.

## Zero-axiom verification

`preservedByReduces` is an induction on `Reduces` (propext-clean — `GradedLambda` plain inductive)
reusing the shipped generic inversions (`HasGradeOver.invertLam`/`invertApp`) and
`hasGradeOver_betaPreservation`; the bundle and witnesses are direct applications.  The usage ω-witness
types through the generic judgment (the carrier `UsageGrade` computes, so the raw App-rule grade is
defeq the stated `[z↦ω, g↦1]`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega` (every declaration probed with `#print axioms` before landing).
Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **Graded subject reduction over the full β-reduction**: a `HasGradeOver R`-typed term keeps its type
AND its EXACT grade vector along every `Reduces` step.  The root-β case is DIM5-7's
`hasGradeOver_betaPreservation` (the corrected App-scaling is what makes grades survive substitution);
the congruence cases invert the typing and reassemble with the IH-preserved grades. -/
theorem HasGradeOver.preservedByReduces {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) :
    ∀ {typeContext : List (GTypeOver R)} {grades : GradeVectorOver R} {resultType : GTypeOver R},
      HasGradeOver R typeContext grades source resultType →
      HasGradeOver R typeContext grades reduct resultType := by
  induction step with
  | beta body argument =>
      intro typeContext grades resultType typed
      exact hasGradeOver_betaPreservation lawful typed
  | congLam body body' _ bodyIH =>
      intro typeContext grades resultType typed
      obtain ⟨binderGrade, domain, codomain, arrowEq, bodyTyped⟩ := HasGradeOver.invertLam typed
      subst arrowEq
      exact HasGradeOver.lam typeContext binderGrade domain codomain grades body' (bodyIH bodyTyped)
  | congAppLeft function function' argument _ functionIH =>
      intro typeContext grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
        gradesEq⟩ := HasGradeOver.invertApp typed
      subst gradesEq
      exact HasGradeOver.app typeContext binderGrade domain resultType functionGrades argumentGrades
        function' argument (functionIH functionTyped) argumentTyped
  | congAppRight function argument argument' _ argumentIH =>
      intro typeContext grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped,
        gradesEq⟩ := HasGradeOver.invertApp typed
      subst gradesEq
      exact HasGradeOver.app typeContext binderGrade domain resultType functionGrades argumentGrades
        function argument' functionTyped (argumentIH argumentTyped)

/-- **The generic metatheory bundle (composition ledger capstone)**: a `HasGradeOver R`-typed term
satisfies BOTH dimensions' metatheory simultaneously, on the SAME reduction relation, independently
derived: strong normalization (TYPE dimension, transferred via grade erasure —
`HasGradeOver.stronglyNormalizing`, DIM5-4) AND graded subject reduction (the GRADED dimension, lifted —
`preservedByReduces`).  The two compose without collision (a SOUND pointwise composition): SN ignores
grades, SR tracks them; neither re-proves the other — for ANY dimension R. -/
theorem HasGradeOver.metatheoryBundle {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {typeContext : List (GTypeOver R)}
    {grades : GradeVectorOver R} {term : GradedLambda} {resultType : GTypeOver R}
    (typed : HasGradeOver R typeContext grades term resultType) :
    GradedLambda.IsStronglyNormalizing term ∧
      ∀ (reduct : GradedLambda), GradedLambda.Reduces term reduct →
        HasGradeOver R typeContext grades reduct resultType :=
  ⟨typed.stronglyNormalizing, fun _ step => HasGradeOver.preservedByReduces lawful step typed⟩

/-! ## Concrete witness `(λx. x) z` at trivial App-scaling `r = R.one`, in any dimension -/

/-- The redex `(λx. x) z` types in `[base]` with the App-rule grade `(z↦0) + R.one · (z↦R.one)` (the
generic linear identity applied to a once-used argument). -/
theorem appliedIdentityOver_typed (R : OrderedGradeSemiring) :
    HasGradeOver R [GTypeOver.base]
      (GradeVectorOver.add (GradeVectorOver.cons R.zero GradeVectorOver.nil)
        (GradeVectorOver.scale R.one (GradeVectorOver.single R 1 0 R.one)))
      (.app (.lam (.var 0)) (.var 0)) GTypeOver.base :=
  HasGradeOver.app (R := R) [GTypeOver.base] R.one GTypeOver.base GTypeOver.base
    (GradeVectorOver.cons R.zero GradeVectorOver.nil)
    (GradeVectorOver.single R 1 0 R.one)
    (.lam (.var 0)) (.var 0)
    (HasGradeOver.lam (R := R) [GTypeOver.base] R.one GTypeOver.base GTypeOver.base
      (GradeVectorOver.cons R.zero GradeVectorOver.nil) (.var 0)
      (HasGradeOver.var (R := R) [GTypeOver.base, GTypeOver.base] 0 GTypeOver.base rfl))
    (HasGradeOver.var (R := R) [GTypeOver.base] 0 GTypeOver.base rfl)

/-- **Concrete grade preservation under a real β-step**, in any dimension: `(λx. x) z ↝ z`, and the
reduct `z` keeps the EXACT grade — the grade accounting survives β through the generic
`preservedByReduces`. -/
theorem appliedIdentityOver_reductKeepsGrade (R : OrderedGradeSemiring)
    (lawful : IsLawfulOrderedGradeSemiring R) :
    HasGradeOver R [GTypeOver.base]
      (GradeVectorOver.add (GradeVectorOver.cons R.zero GradeVectorOver.nil)
        (GradeVectorOver.scale R.one (GradeVectorOver.single R 1 0 R.one)))
      (GradedLambda.var 0) GTypeOver.base :=
  HasGradeOver.preservedByReduces lawful
    (GradedLambda.Reduces.beta (GradedLambda.var 0) (GradedLambda.var 0))
    (appliedIdentityOver_typed R)

/-- DIM5-8: the SECURITY dimension's `(λx. x) z ↝ z` keeps its security grade — no security-specific
proof, the generic witness at `fxSecuritySemiring`. -/
theorem securityAppliedIdentity_reductKeepsGrade :
    HasGradeOver fxSecuritySemiring [GTypeOver.base]
      (GradeVectorOver.add (GradeVectorOver.cons fxSecuritySemiring.zero GradeVectorOver.nil)
        (GradeVectorOver.scale fxSecuritySemiring.one
          (GradeVectorOver.single fxSecuritySemiring 1 0 fxSecuritySemiring.one)))
      (GradedLambda.var 0) GTypeOver.base :=
  appliedIdentityOver_reductKeepsGrade fxSecuritySemiring fxSecuritySemiring_isLawful

/-- DIM5-8: the USAGE dimension's `(λx. x) z ↝ z` keeps its usage grade — the SAME generic witness at
`fxUsageSemiring`.  Two dimensions, one composition ledger. -/
theorem usageAppliedIdentity_reductKeepsGrade :
    HasGradeOver fxUsageSemiring [GTypeOver.base]
      (GradeVectorOver.add (GradeVectorOver.cons fxUsageSemiring.zero GradeVectorOver.nil)
        (GradeVectorOver.scale fxUsageSemiring.one
          (GradeVectorOver.single fxUsageSemiring 1 0 fxUsageSemiring.one)))
      (GradedLambda.var 0) GTypeOver.base :=
  appliedIdentityOver_reductKeepsGrade fxUsageSemiring fxUsageSemiring_isLawful

/-- DIM5-8: the metatheory bundle at the security dimension on `(λx. x) z` — it is SN AND every reduct
keeps the grade.  The capstone witness: SN ∧ graded-SR on the same term, in a second dimension. -/
theorem securityMetatheoryBundle_smoke :
    GradedLambda.IsStronglyNormalizing (.app (.lam (.var 0)) (.var 0)) ∧
      ∀ (reduct : GradedLambda),
        GradedLambda.Reduces (.app (.lam (.var 0)) (.var 0)) reduct →
        HasGradeOver fxSecuritySemiring [GTypeOver.base]
          (GradeVectorOver.add (GradeVectorOver.cons fxSecuritySemiring.zero GradeVectorOver.nil)
            (GradeVectorOver.scale fxSecuritySemiring.one
              (GradeVectorOver.single fxSecuritySemiring 1 0 fxSecuritySemiring.one)))
          reduct GTypeOver.base :=
  HasGradeOver.metatheoryBundle fxSecuritySemiring_isLawful (appliedIdentityOver_typed fxSecuritySemiring)

/-! ## The decisive `r = ω` regression at usage, routed through the GENERIC `preservedByReduces` -/

/-- A binary (curried) function type `g : base -(1)-> (base -(1)-> base)` over the usage semiring. -/
def omegaScalingBinaryTypeUsage : GTypeOver fxUsageSemiring :=
  .arrow UsageGrade.one GTypeOver.base (.arrow UsageGrade.one GTypeOver.base GTypeOver.base)

/-- **The ω-scaling redex `(λx. (g x) x) z` types at the EXACT grade `[z↦ω, g↦1]`** in the generic
judgment at `fxUsageSemiring`.  Because the binder `x` is used `ω` times, the App rule scales the
once-occurring argument `z`'s usage by `ω`, so `z` already carries `ω` in the redex — the non-trivial
App-scaling (`r = ω`) that the generic machinery must get right (`UsageGrade` computes, so the raw
App-rule grade is defeq the stated `[z↦ω, g↦1]`). -/
theorem usageOmegaScalingRedex_typed :
    HasGradeOver fxUsageSemiring [GTypeOver.base, omegaScalingBinaryTypeUsage]
      (GradeVectorOver.cons UsageGrade.omega (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil))
      (.app (.lam (.app (.app (.var 2) (.var 0)) (.var 0))) (.var 0)) GTypeOver.base :=
  HasGradeOver.app (R := fxUsageSemiring) [GTypeOver.base, omegaScalingBinaryTypeUsage]
    UsageGrade.omega GTypeOver.base GTypeOver.base
    (GradeVectorOver.cons UsageGrade.zero (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil))
    (GradeVectorOver.single fxUsageSemiring 2 0 UsageGrade.one)
    (.lam (.app (.app (.var 2) (.var 0)) (.var 0))) (.var 0)
    (HasGradeOver.lam (R := fxUsageSemiring) [GTypeOver.base, omegaScalingBinaryTypeUsage]
      UsageGrade.omega GTypeOver.base GTypeOver.base
      (GradeVectorOver.cons UsageGrade.zero (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil))
      (.app (.app (.var 2) (.var 0)) (.var 0))
      (HasGradeOver.app (R := fxUsageSemiring)
        [GTypeOver.base, GTypeOver.base, omegaScalingBinaryTypeUsage] UsageGrade.one GTypeOver.base
        GTypeOver.base
        (GradeVectorOver.add (GradeVectorOver.single fxUsageSemiring 3 2 UsageGrade.one)
          (GradeVectorOver.scale UsageGrade.one
            (GradeVectorOver.single fxUsageSemiring 3 0 UsageGrade.one)))
        (GradeVectorOver.single fxUsageSemiring 3 0 UsageGrade.one)
        (.app (.var 2) (.var 0)) (.var 0)
        (HasGradeOver.app (R := fxUsageSemiring)
          [GTypeOver.base, GTypeOver.base, omegaScalingBinaryTypeUsage] UsageGrade.one GTypeOver.base
          (.arrow UsageGrade.one GTypeOver.base GTypeOver.base)
          (GradeVectorOver.single fxUsageSemiring 3 2 UsageGrade.one)
          (GradeVectorOver.single fxUsageSemiring 3 0 UsageGrade.one) (.var 2) (.var 0)
          (HasGradeOver.var (R := fxUsageSemiring)
            [GTypeOver.base, GTypeOver.base, omegaScalingBinaryTypeUsage] 2
            omegaScalingBinaryTypeUsage rfl)
          (HasGradeOver.var (R := fxUsageSemiring)
            [GTypeOver.base, GTypeOver.base, omegaScalingBinaryTypeUsage] 0 GTypeOver.base rfl))
        (HasGradeOver.var (R := fxUsageSemiring)
          [GTypeOver.base, GTypeOver.base, omegaScalingBinaryTypeUsage] 0 GTypeOver.base rfl)))
    (HasGradeOver.var (R := fxUsageSemiring) [GTypeOver.base, omegaScalingBinaryTypeUsage] 0
      GTypeOver.base rfl)

/-- **After `(λx. (g x) x) z ↝ (g z) z`, the contractum keeps the EXACT grade `[z↦ω, g↦1]`** — via the
GENERIC `preservedByReduces`.  The `ω`-scaling survives β: `z`, occurring once in the redex, is correctly
tracked at `ω` once the binder duplicates it.  The decisive regression that the GENERIC substitution-grade
law is `ρ + r · σ` (not `+`-only / scale-by-1) — for the saturating usage semiring, through the shared
machinery. -/
theorem usageOmegaScalingRedex_reductKeepsGrade :
    HasGradeOver fxUsageSemiring [GTypeOver.base, omegaScalingBinaryTypeUsage]
      (GradeVectorOver.cons UsageGrade.omega (GradeVectorOver.cons UsageGrade.one GradeVectorOver.nil))
      (.app (.app (.var 1) (.var 0)) (.var 0)) GTypeOver.base :=
  HasGradeOver.preservedByReduces fxUsageSemiring_isLawful
    (GradedLambda.Reduces.beta (.app (.app (.var 2) (.var 0)) (.var 0)) (.var 0))
    usageOmegaScalingRedex_typed

end FX1Poly.Modal
