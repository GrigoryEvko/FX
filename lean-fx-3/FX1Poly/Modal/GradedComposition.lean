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
    the two compose without collision (Usage × Type is a SOUND pointwise composition, NOT one of the
    §6.8 collision pairs — the orthogonality claim here is for this specific pair, not all 21).
  * `appliedIdentity_*` / `omegaScalingRedex_*` — concrete non-vacuous β witnesses, each keeping the
    EXACT grade across a real β-step.  `appliedIdentity` (`(λx. x) z ↝ z`, `[z↦1]`) exercises the
    App-rule accounting at `r = 1` (trivial multiply-by-1); `omegaScalingRedex`
    (`(λx. (g x) x) z ↝ (g z) z`) drives it at `r = ω` — the bound `x` is used twice, so the App rule
    scales the once-occurring `z`'s usage by `ω`, and `z` is correctly tracked at `ω` after β
    duplicates it (`[z↦ω, g↦1]` preserved exactly).  The `ω` case is the regression test that
    distinguishes the correct `ρ + r·σ` substitution-grade law from a `+`-only (or scale-by-1) bug.

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
dimensions compose without collision (Usage × Type is a SOUND pointwise composition, not a §6.8
collision pair): SN ignores grades, SR tracks them; neither re-proves the other. -/
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
EXACT grade vector `[z ↦ 1]` — the grade accounting survives β.  A non-vacuous witness of
`preservedByReduces` at App-scaling `r = 1` (a trivial multiply-by-1; the non-trivial `r = ω` scaling
is exercised by `omegaScalingRedex_*` below). -/
theorem appliedIdentity_reductKeepsGrade :
    HasUsage [GType.base]
      (GradeVector.add (GradeVector.cons UsageGrade.zero GradeVector.nil)
        (GradeVector.scale UsageGrade.one (GradeVector.single 1 0 UsageGrade.one)))
      (GradedLambda.var 0) GType.base :=
  HasUsage.preservedByReduces (GradedLambda.Reduces.beta (GradedLambda.var 0) (GradedLambda.var 0))
    appliedIdentity_typed

/-- A binary (curried) function type `g : base -(1)-> (base -(1)-> base)` — each argument linear. -/
def omegaScalingBinaryType : GType := .arrow .one .base (.arrow .one .base .base)

/-- The graded redex `(λx. (g x) x) z` in context `[z: base, g: omegaScalingBinaryType]` (de Bruijn
z=0, g=1).  Under `λx`, the bound `x` (de Bruijn 0) is used TWICE, so its binder grade is `ω`. -/
def omegaScalingRedex : GradedLambda :=
  .app (.lam (.app (.app (.var 2) (.var 0)) (.var 0))) (.var 0)

/-- Its β-contractum `(g z) z` — the bound `x` having been replaced by `z`, which now occurs twice. -/
def omegaScalingContractum : GradedLambda := .app (.app (.var 1) (.var 0)) (.var 0)

/-- **The ω-scaling redex types at the EXACT grade `[z↦ω, g↦1]`.**  Because the binder `x` is used `ω`
times, the App rule scales the once-occurring argument `z`'s usage by `ω`, so `z` already carries `ω`
in the redex.  This is the non-trivial App-scaling (`r = ω`) that `appliedIdentity` (`r = 1`) cannot
exercise. -/
theorem omegaScalingRedex_typed :
    HasUsage [GType.base, omegaScalingBinaryType]
      (GradeVector.cons UsageGrade.omega (GradeVector.cons UsageGrade.one GradeVector.nil))
      omegaScalingRedex GType.base :=
  HasUsage.app [GType.base, omegaScalingBinaryType] UsageGrade.omega GType.base GType.base
    (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil))
    (GradeVector.single 2 0 UsageGrade.one)
    (.lam (.app (.app (.var 2) (.var 0)) (.var 0))) (.var 0)
    (HasUsage.lam [GType.base, omegaScalingBinaryType] UsageGrade.omega GType.base GType.base
      (GradeVector.cons UsageGrade.zero (GradeVector.cons UsageGrade.one GradeVector.nil))
      (.app (.app (.var 2) (.var 0)) (.var 0))
      (HasUsage.app [GType.base, GType.base, omegaScalingBinaryType] UsageGrade.one GType.base
        GType.base
        (GradeVector.add (GradeVector.single 3 2 UsageGrade.one)
          (GradeVector.scale UsageGrade.one (GradeVector.single 3 0 UsageGrade.one)))
        (GradeVector.single 3 0 UsageGrade.one)
        (.app (.var 2) (.var 0)) (.var 0)
        (HasUsage.app [GType.base, GType.base, omegaScalingBinaryType] UsageGrade.one GType.base
          (.arrow UsageGrade.one GType.base GType.base)
          (GradeVector.single 3 2 UsageGrade.one) (GradeVector.single 3 0 UsageGrade.one)
          (.var 2) (.var 0)
          (HasUsage.var [GType.base, GType.base, omegaScalingBinaryType] 2 omegaScalingBinaryType rfl)
          (HasUsage.var [GType.base, GType.base, omegaScalingBinaryType] 0 GType.base rfl))
        (HasUsage.var [GType.base, GType.base, omegaScalingBinaryType] 0 GType.base rfl)))
    (HasUsage.var [GType.base, omegaScalingBinaryType] 0 GType.base rfl)

/-- **After the β-step `(λx. (g x) x) z ↝ (g z) z`, the contractum keeps the EXACT grade `[z↦ω, g↦1]`.**
The `ω`-scaling survives β: `z`, occurring once in the redex, is correctly tracked at `ω` once the
binder duplicates it.  The decisive non-trivial-scaling SR regression witness — it would FAIL if the
substitution-grade law used `+` (or scale-by-1) instead of the correct `ρ + r·σ`. -/
theorem omegaScalingRedex_reductKeepsGrade :
    HasUsage [GType.base, omegaScalingBinaryType]
      (GradeVector.cons UsageGrade.omega (GradeVector.cons UsageGrade.one GradeVector.nil))
      omegaScalingContractum GType.base :=
  HasUsage.preservedByReduces
    (GradedLambda.Reduces.beta (.app (.app (.var 2) (.var 0)) (.var 0)) (.var 0))
    omegaScalingRedex_typed

/-- Independent cross-check: typing the contractum `(g z) z` directly from scratch ALSO yields exactly
`[z↦ω, g↦1]` (`z` used twice after the duplication) — so the grade preserved by `preservedByReduces`
is genuinely `[z↦ω, g↦1]`, not a coincidence of the substitution machinery. -/
theorem omegaScalingContractum_typedDirectly :
    HasUsage [GType.base, omegaScalingBinaryType]
      (GradeVector.cons UsageGrade.omega (GradeVector.cons UsageGrade.one GradeVector.nil))
      omegaScalingContractum GType.base :=
  HasUsage.app [GType.base, omegaScalingBinaryType] UsageGrade.one GType.base GType.base
    (GradeVector.add (GradeVector.single 2 1 UsageGrade.one)
      (GradeVector.scale UsageGrade.one (GradeVector.single 2 0 UsageGrade.one)))
    (GradeVector.single 2 0 UsageGrade.one)
    (.app (.var 1) (.var 0)) (.var 0)
    (HasUsage.app [GType.base, omegaScalingBinaryType] UsageGrade.one GType.base
      (.arrow UsageGrade.one GType.base GType.base)
      (GradeVector.single 2 1 UsageGrade.one) (GradeVector.single 2 0 UsageGrade.one)
      (.var 1) (.var 0)
      (HasUsage.var [GType.base, omegaScalingBinaryType] 1 omegaScalingBinaryType rfl)
      (HasUsage.var [GType.base, omegaScalingBinaryType] 0 GType.base rfl))
    (HasUsage.var [GType.base, omegaScalingBinaryType] 0 GType.base rfl)

end FX1Poly.Modal
