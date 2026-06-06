import FX1Poly.Modal.GradedFundamentalTheorem
import FX1Poly.Modal.GradedSubjectReduction

/-! # FX1Poly/Modal/GradedComposition — the DIM2 composition ledger (DIM2-7)

The thesis-validation capstone for the usage dimension.  FX's headline claim (§1.1, §6.8) is that the
21 graded dimensions compose pointwise.  DIM2 instantiated a SECOND graded dimension (usage `{0,1,ω}`)
atop the type dimension and showed it composes WITHOUT cascading the type metatheory:

  * **No cascade into the type engine** — STRUCTURAL FACT (auditable, not a Lean theorem): every DIM2
    declaration lives under `FX1Poly/Modal/` over its own `GradedLambda`/`HasUsage`; the kernel's
    194-generator `FX1Poly.Core` and the dependent type engine `FX1Poly.Typed` received ZERO new arms.
  * **SN is OBTAINED, not re-proved** — `HasUsage.stronglyNormalizing` (DIM2-5) factors through grade
    erasure to the type dimension's STLC-SN; no graded-reducibility relation was built.
  * **The usage dimension's OWN metatheory is orthogonal** — graded subject reduction tracks grades,
    which the SN/type dimension ignores.  This file lifts DIM2-3's root-β SR to the full β-reduction
    and bundles both dimensions' metatheory on the SAME reduction relation.

  * `HasUsage.preservedByReduces` — **graded subject reduction over the full β-reduction `Reduces`**: a
    `HasUsage`-typed term keeps its type AND its exact grade vector along every β-step (root-β via
    DIM2-3's `hasUsage_betaPreservation`; congruence cases by inversion + grade-preserving reassembly).
  * `HasUsage.metatheoryBundle` — **the capstone**: a typed term satisfies BOTH dimensions' metatheory
    simultaneously and independently — strong normalization (type dimension, transferred) AND graded
    subject reduction (usage dimension, lifted) — on the same `Reduces`.  Neither re-proves the other;
    they do not collide.
  * `appliedIdentity_*` — a concrete non-vacuous witness: `(λx. x) z ↝ z` keeps the exact grade
    `[z ↦ 1]`, exercising the App-scaling accounting through a real β-step.

## Zero-axiom verification

`preservedByReduces` is an induction on `Reduces` (propext-clean — `GradedLambda` plain inductive)
reusing the shipped inversions (`HasUsage.invertLam`/`invertApp`) and `hasUsage_betaPreservation`; the
bundle and smoke witnesses are direct applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **Graded subject reduction over the full β-reduction**: a `HasUsage`-typed term keeps its type AND
its EXACT grade vector along every `Reduces` step.  The root-β case is DIM2-3's `hasUsage_betaPreservation`
(the corrected App-scaling is what makes grades survive substitution); the congruence cases invert the
typing and reassemble with the IH-preserved grades. -/
theorem HasUsage.preservedByReduces {source reduct : GradedLambda}
    (step : GradedLambda.Reduces source reduct) :
    ∀ {typeContext : List GType} {grades : GradeVector} {resultType : GType},
      HasUsage typeContext grades source resultType →
      HasUsage typeContext grades reduct resultType := by
  induction step with
  | beta body argument =>
      intro typeContext grades resultType typed
      exact hasUsage_betaPreservation typed
  | congLam body body' _ bodyIH =>
      intro typeContext grades resultType typed
      obtain ⟨binderGrade, domain, codomain, arrowEq, bodyTyped⟩ := HasUsage.invertLam typed
      subst arrowEq
      exact HasUsage.lam typeContext binderGrade domain codomain grades body' (bodyIH bodyTyped)
  | congAppLeft function function' argument _ functionIH =>
      intro typeContext grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, gradesEq⟩ :=
        HasUsage.invertApp typed
      subst gradesEq
      exact HasUsage.app typeContext binderGrade domain resultType functionGrades argumentGrades
        function' argument (functionIH functionTyped) argumentTyped
  | congAppRight function argument argument' _ argumentIH =>
      intro typeContext grades resultType typed
      obtain ⟨binderGrade, domain, functionGrades, argumentGrades, functionTyped, argumentTyped, gradesEq⟩ :=
        HasUsage.invertApp typed
      subst gradesEq
      exact HasUsage.app typeContext binderGrade domain resultType functionGrades argumentGrades
        function argument' functionTyped (argumentIH argumentTyped)

/-- **The DIM2 metatheory bundle (composition ledger capstone)**: a `HasUsage`-typed term satisfies
BOTH dimensions' metatheory simultaneously, on the SAME reduction relation, independently derived:
strong normalization (TYPE dimension, transferred via grade erasure — `HasUsage.stronglyNormalizing`)
AND graded subject reduction (USAGE dimension, lifted from DIM2-3 — `preservedByReduces`).  The two
dimensions compose without collision: SN ignores grades, SR tracks them; neither re-proves the other. -/
theorem HasUsage.metatheoryBundle {typeContext : List GType} {grades : GradeVector}
    {term : GradedLambda} {resultType : GType} (typed : HasUsage typeContext grades term resultType) :
    GradedLambda.IsStronglyNormalizing term ∧
      ∀ (reduct : GradedLambda), GradedLambda.Reduces term reduct →
        HasUsage typeContext grades reduct resultType :=
  ⟨typed.stronglyNormalizing, fun _ step => HasUsage.preservedByReduces step typed⟩

/-- A concrete graded redex `(λx. x) z` with `z` free (de Bruijn `0`), in context `[base]`: `z` is
used exactly once. -/
def appliedIdentity : GradedLambda := .app (.lam (.var 0)) (.var 0)

/-- The redex types in `[base]` with grade `[z ↦ 1]` (the App rule scales the linear identity's binder
grade `1` over the argument's usage `1`). -/
theorem appliedIdentity_typed :
    HasUsage [GType.base]
      (GradeVector.add (GradeVector.cons UsageGrade.zero GradeVector.nil)
        (GradeVector.scale UsageGrade.one (GradeVector.single 1 0 UsageGrade.one)))
      appliedIdentity GType.base :=
  HasUsage.app [GType.base] UsageGrade.one GType.base GType.base
    (GradeVector.cons UsageGrade.zero GradeVector.nil)
    (GradeVector.single 1 0 UsageGrade.one)
    (.lam (.var 0)) (.var 0)
    (HasUsage.lam [GType.base] UsageGrade.one GType.base GType.base
      (GradeVector.cons UsageGrade.zero GradeVector.nil) (.var 0)
      (HasUsage.var [GType.base, GType.base] 0 GType.base rfl))
    (HasUsage.var [GType.base] 0 GType.base rfl)

/-- **Concrete grade preservation under a real β-step**: `(λx. x) z ↝ z`, and the reduct `z` keeps the
EXACT grade vector `[z ↦ 1]` — the App-scaling accounting survives β.  A non-vacuous witness of
`preservedByReduces`. -/
theorem appliedIdentity_reductKeepsGrade :
    HasUsage [GType.base]
      (GradeVector.add (GradeVector.cons UsageGrade.zero GradeVector.nil)
        (GradeVector.scale UsageGrade.one (GradeVector.single 1 0 UsageGrade.one)))
      (GradedLambda.var 0) GType.base :=
  HasUsage.preservedByReduces (GradedLambda.Reduces.beta (GradedLambda.var 0) (GradedLambda.var 0))
    appliedIdentity_typed

end FX1Poly.Modal
