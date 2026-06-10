import FX1Poly.Typed.UnitReadbackDeepSpineBoundary
import FX1Poly.Core.StepInversion

/-! # FX1Poly/Typed/UnitReadbackAnnotationBoundary
   — ★ the 9th boundary: the λ arm's SYNTACTIC annotation match (#481 brick-7 verdict)

The mandated post-spine completeness re-analysis, machine-checked.  The λ arm fires only when
the subject's domain annotation is SYNTACTICALLY the classifier's literal domain — but typed λs
may carry annotations that merely CONVERT to it.  Witness, in the EMPTY context:

  * `redexAnnotation` = `app(λ(x:Type@0).x, Unit)` — a β-redex grown-typed at `Type@0` that
    contracts to `Unit` in one step.
  * `λ(redexAnnotation).x₀` and `λ(Unit).x₀` are BOTH grown-typed at `Π(_:Unit).Unit` (the
    redex side via `conv` through the Π-code congruence step) — the FIRST boundary pair with
    both endpoints typed at one formation-typed classifier, so `ofReadbackEqual` is fully
    applicable... and misses: the annotation-mismatch arm degrades the left side to the deep
    collapse (which fixes it — the binder's unit-typedness hides BEHIND the redex, so the
    body variable is not rewritten), while the right side computes the η-long `λ(Unit).unit`.
  * The readbacks are distinct at every fuel pair AND never βη-join (the left's reducts all
    keep the VARIABLE body — the star-chain invariant — while the right's body is `unit`).

## What this boundary is — and is not

The PAIR is decidable by the shipped βη machinery (`annotationLambdas_oneStepApart`: one
congruence step joins them; the `Cong` witness below IS `ofBetaEtaConv`).  What fails is the
READBACK as a canonicalizer: a normalize-and-compare decider built on it (#364) would compute
distinct never-joining forms for definitionally equal, identically-classified subjects.  The
9th boundary is about CANONICAL-FORM completeness, not pair-decidability.

## The verdict — trust the classifier (brick 7)

The fix is the standard NbE discipline: the λ arm should not COMPARE annotations at all — it
should EMIT the classifier's domain and descend unconditionally, re-typing the body across the
binder via grown context-conversion (`invertLam` + Π-code injectivity supply `Conv domainAnn
domainCode`; the classifier's formation inversion types the new entry).  That also makes
readback outputs annotation-canonical — the η-long form's binder annotations come from the
classifier, exactly like the η-expansion arm already does.

## Zero-axiom verification

Typings are `piIntro`/`piElim`/`conv` chains with one-step `Conv` witnesses; the never-join is
a `betaEtaStar` invariant (variable-bodied λs stay variable-bodied) over `Step.from_lam` +
`Step.no_step_from_var` + root-η refutation, closed by the Boolean body projector; readback
computations are `rfl` per fuel shape; inequalities are `decide`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- `app(λ(x:Type@0).x, Unit)` — a β-redex that contracts to `Unit`: the non-literal,
Conv-to-`Unit` domain annotation. -/
def redexAnnotation {scope : Nat} : RawTerm scope :=
  appCell
    (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (variableCell ⟨0, Nat.zero_lt_succ scope⟩))
    unitTypeCell

/-- `λ(redexAnnotation).x₀` — the λ whose annotation merely CONVERTS to the classifier's
domain. -/
def annotatedByRedex : RawTerm 0 :=
  lamCell redexAnnotation (variableCell ⟨0, Nat.zero_lt_one⟩)

/-- `λ(Unit).x₀` — the literally-annotated twin. -/
def annotatedByLiteral : RawTerm 0 :=
  lamCell unitTypeCell (variableCell ⟨0, Nat.zero_lt_one⟩)

/-- The redex annotation contracts to `Unit` in one β step (at every scope — the λ body is the
innermost variable, so `subst0` computes). -/
theorem redexAnnotation_steps {scope : Nat} :
    Step (redexAnnotation : RawTerm scope) unitTypeCell :=
  Step.beta

/-- The redex annotation is grown-typed at `Type@0` — `piElim` of the identity-on-`Type@0` λ
at the `Unit` code. -/
theorem redexAnnotationTyped (profile : PolyProfile) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      redexAnnotation (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.piIntro LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc UniverseFlag.standard
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation TypingContext.empty
          LevelExpr.lzero UniverseFlag.standard))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation
          (TypingContext.empty.cons
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
          LevelExpr.lzero UniverseFlag.standard))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.var
          (TypingContext.empty.cons
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
          ⟨0, Nat.zero_lt_one⟩)))
    (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped TypingContext.empty))

/-- `λ(redexAnnotation).x₀` is grown-typed at the REDEX-annotated Π code — the body variable's
looked-up classifier (the weakened redex) converts to `Unit`. -/
theorem annotatedByRedexTypedAtRedexPi (profile : PolyProfile) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      annotatedByRedex (piTyCodeCell redexAnnotation unitTypeCell) :=
  HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
    (redexAnnotationTyped profile)
    (HasTypeDescPi.ofFormation
      (unitTypeCellFormationTyped (TypingContext.empty.cons redexAnnotation)))
    (HasTypeDescPi.conv LevelExpr.lzero UniverseFlag.standard
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.var (TypingContext.empty.cons redexAnnotation) ⟨0, Nat.zero_lt_one⟩))
      ⟨unitTypeCell, StepStar.trans redexAnnotation_steps (StepStar.refl _),
        StepStar.refl _⟩
      (HasTypeDescPi.ofFormation
        (unitTypeCellFormationTyped (TypingContext.empty.cons redexAnnotation))))

/-- The two Π codes are one congruence step apart — the domain child fires its β redex. -/
theorem annotationPiCodes_oneStepApart :
    Step (piTyCodeCell redexAnnotation unitTypeCell : RawTerm 0)
      (piTyCodeCell unitTypeCell unitTypeCell) :=
  Step.cong .gen_piTyCode ()
    (StepChildren.here (.childCons unitTypeCell .childNil) redexAnnotation_steps)

/-- **The redex-annotated λ is grown-typed at the LITERAL classifier `Π(_:Unit).Unit`** —
`conv` through the Π-code congruence step. -/
theorem annotatedByRedexTyped (profile : PolyProfile) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      annotatedByRedex (piTyCodeCell unitTypeCell unitTypeCell) :=
  HasTypeDescPi.conv (LevelExpr.lmax LevelExpr.lzero LevelExpr.lzero) UniverseFlag.standard
    (annotatedByRedexTypedAtRedexPi profile)
    ⟨piTyCodeCell unitTypeCell unitTypeCell,
      StepStar.trans annotationPiCodes_oneStepApart (StepStar.refl _),
      StepStar.refl _⟩
    (HasTypeDescPi.ofFormation
      (hasTypeDesc_piFormation_viaGenArm TypingContext.empty
        unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
        (unitTypeCellFormationTyped TypingContext.empty)
        (unitTypeCellFormationTyped (TypingContext.empty.cons unitTypeCell))))

/-- The literally-annotated twin is grown-typed at the same classifier, directly. -/
theorem annotatedByLiteralTyped (profile : PolyProfile) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      annotatedByLiteral (piTyCodeCell unitTypeCell unitTypeCell) :=
  HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
    (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped TypingContext.empty))
    (HasTypeDescPi.ofFormation
      (unitTypeCellFormationTyped (TypingContext.empty.cons unitTypeCell)))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (TypingContext.empty.cons unitTypeCell) ⟨0, Nat.zero_lt_one⟩))

/-- The λs themselves are one congruence step apart — the annotation child fires its redex. -/
theorem annotationLambdas_oneStepApart :
    Step annotatedByRedex annotatedByLiteral :=
  Step.cong .gen_lam ()
    (StepChildren.here (.childCons (variableCell ⟨0, Nat.zero_lt_one⟩) .childNil)
      redexAnnotation_steps)

/-- **The pair is congruently unit-η-equal** — in fact already βη-judgmentally equal: both
endpoints typed at `Π(_:Unit).Unit` and joined by the one congruence step. -/
theorem annotationPair_congruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (TypingContext.empty : TypingContext profile 0)
      annotatedByRedex annotatedByLiteral :=
  DefEqUnitEtaCong.ofDefEq
    (.ofBetaEtaConv WfContextDesc.emptyIsWellFormed
      (annotatedByRedexTyped profile) (annotatedByLiteralTyped profile)
      ⟨annotatedByLiteral,
        Step.betaEtaStar.trans (Or.inl annotationLambdas_oneStepApart)
          (Step.betaEtaStar.refl _),
        Step.betaEtaStar.refl _⟩)

/-- The annotation-mismatch arm FIXES the redex-annotated λ at every fuel: the deep collapse
cannot rewrite the body variable (its looked-up classifier is the weakened REDEX, not the
literal `unitTypeCell`), so the readback returns the input unchanged. -/
theorem readback_annotatedByRedex_isFixed (profile : PolyProfile) :
    ∀ fuel : Nat,
      readbackAtClassifier fuel (TypingContext.empty : TypingContext profile 0)
          (piTyCodeCell unitTypeCell unitTypeCell) annotatedByRedex
        = annotatedByRedex
  | 0 => rfl
  | _ + 1 => rfl

/-- The literal twin computes to the η-long form `λ(Unit).unit` at every fuel. -/
theorem readback_annotatedByLiteral_isEtaLong (profile : PolyProfile) :
    ∀ fuel : Nat,
      readbackAtClassifier fuel (TypingContext.empty : TypingContext profile 0)
          (piTyCodeCell unitTypeCell unitTypeCell) annotatedByLiteral
        = lamCell unitTypeCell unitCell
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- Does this term carry a VARIABLE directly under a λ binder?  The Boolean projector that
separates the two readback outputs through equalities. -/
def hasVariableBodyUnderLam {scope : Nat} (term : RawTerm scope) : Bool :=
  match asLamCell? term with
  | some (_, body) => (asVarCell? body).isSome
  | none => false

/-- **The star-chain invariant**: every βη reduct of a variable-bodied λ is a variable-bodied
λ — annotation children may step, the body variable cannot, root η needs an application body,
and the other η sources are not λ cells. -/
theorem betaEtaStar_preservesVariableBodiedLambda {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : Step.betaEtaStar sourceTerm targetTerm) :
    (∃ domainAnn, sourceTerm
        = lamCell domainAnn (variableCell ⟨0, Nat.zero_lt_succ scope⟩)) →
    ∃ domainAnn, targetTerm
        = lamCell domainAnn (variableCell ⟨0, Nat.zero_lt_succ scope⟩) := by
  induction chain with
  | refl _ => exact id
  | trans single _rest ih =>
      intro sourceShape
      obtain ⟨domainAnn, sourceIsLam⟩ := sourceShape
      subst sourceIsLam
      cases single with
      | inl step =>
          cases Step.from_lam step with
          | inl domainStepped =>
              obtain ⟨domainAfter, targetShape, _domainStep⟩ := domainStepped
              exact ih ⟨domainAfter, targetShape⟩
          | inr bodyStepped =>
              obtain ⟨_, _, bodyStep⟩ := bodyStepped
              exact absurd bodyStep Step.no_step_from_var
      | inr etaStep => cases etaStep

/-- **The readback outputs never βη-join**: every reduct of the fixed redex-annotated λ keeps
its VARIABLE body, while the η-long form's body is the `unit` value — and the η-long form is
βη-normal, so any common reduct must BE it. -/
theorem annotationReadbackForms_notBetaEtaConv :
    ¬ BetaEtaConv annotatedByRedex (lamCell unitTypeCell unitCell) := by
  intro convertible
  obtain ⟨commonTerm, redexChain, etaLongChain⟩ := convertible
  have etaLongIsCommon :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        (lamCell unitTypeCell unitCell : RawTerm 0).reduceOnceBetaEta = none))
      etaLongChain
  obtain ⟨survivingAnnotation, commonIsVariableBodied⟩ :=
    betaEtaStar_preservesVariableBodiedLambda redexChain ⟨redexAnnotation, rfl⟩
  exact absurd
    (show false = true from
      congrArg hasVariableBodyUnderLam (etaLongIsCommon.trans commonIsVariableBodied))
    (by decide)

/-- **★ The 9th boundary — the readback is incomplete at ANNOTATION-MISMATCH λs**: a pair of
λ-terms BOTH grown-typed at the same formation-typed classifier `Π(_:Unit).Unit` in the wf
empty context (so `ofReadbackEqual` is fully applicable), congruently unit-η-equal (indeed
βη-equal in one congruence step), whose readbacks at EVERY fuel pair are distinct and never
βη-join — no normalize-and-compare decider built on the current readback closes it.  The λ
arm must TRUST THE CLASSIFIER (emit its domain, descend unconditionally) — brick 7. -/
theorem readback_isIncompleteAtAnnotationMismatch (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 0),
      DefEqUnitEtaCong profile (TypingContext.empty : TypingContext profile 0)
        leftTerm rightTerm ∧
      HasTypeDescPi profile TypingContext.empty leftTerm
        (piTyCodeCell unitTypeCell unitTypeCell) ∧
      HasTypeDescPi profile TypingContext.empty rightTerm
        (piTyCodeCell unitTypeCell unitTypeCell) ∧
      (∀ leftFuel rightFuel : Nat,
        readbackAtClassifier leftFuel (TypingContext.empty : TypingContext profile 0)
            (piTyCodeCell unitTypeCell unitTypeCell) leftTerm
          ≠ readbackAtClassifier rightFuel (TypingContext.empty : TypingContext profile 0)
              (piTyCodeCell unitTypeCell unitTypeCell) rightTerm) ∧
      (∀ leftFuel rightFuel : Nat,
        ¬ BetaEtaConv
          (readbackAtClassifier leftFuel (TypingContext.empty : TypingContext profile 0)
            (piTyCodeCell unitTypeCell unitTypeCell) leftTerm)
          (readbackAtClassifier rightFuel (TypingContext.empty : TypingContext profile 0)
            (piTyCodeCell unitTypeCell unitTypeCell) rightTerm)) :=
  ⟨annotatedByRedex, annotatedByLiteral,
    annotationPair_congruentlyEqual profile,
    annotatedByRedexTyped profile,
    annotatedByLiteralTyped profile,
    fun leftFuel rightFuel readbacksEqual =>
      absurd
        (show annotatedByRedex = lamCell unitTypeCell unitCell from
          (readback_annotatedByRedex_isFixed profile leftFuel).symm.trans
            (readbacksEqual.trans
              (readback_annotatedByLiteral_isEtaLong profile rightFuel)))
        (by decide),
    fun leftFuel rightFuel convertible =>
      annotationReadbackForms_notBetaEtaConv
        (readback_annotatedByRedex_isFixed profile leftFuel ▸
          readback_annotatedByLiteral_isEtaLong profile rightFuel ▸ convertible)⟩

end FX1Poly.Typed
