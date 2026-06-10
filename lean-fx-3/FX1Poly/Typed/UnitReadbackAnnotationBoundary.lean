import FX1Poly.Typed.UnitReadbackDeepSpineBoundary
import FX1Poly.Core.StepInversion

/-! # FX1Poly/Typed/UnitReadbackAnnotationBoundary
   — ★ the 9th boundary, DECIDED: trust-the-classifier annotation canonicalization (#481 brick 7)

The post-spine completeness re-analysis found the λ arm's SYNTACTIC annotation match: typed λs
may carry annotations that merely CONVERT to the classifier's literal domain.  Witness, in the
EMPTY context:

  * `redexAnnotation` = `app(λ(x:Type@0).x, Unit)` — a β-redex grown-typed at `Type@0` that
    contracts to `Unit` in one step.
  * `λ(redexAnnotation).x₀` and `λ(Unit).x₀` are BOTH grown-typed at `Π(_:Unit).Unit` (the
    redex side via `conv` through the Π-code congruence step) — the FIRST boundary pair with
    both endpoints typed at one formation-typed classifier.
  * Against the FROZEN deep-collapse ingredient the boundary stands permanently
    (`deepCollapseMode_isIncompleteAtAnnotationMismatch`): the collapse's syntactic lookup test
    cannot see unit-typedness BEHIND the redex, and the collapses are distinct forms that never
    βη-join (the star-chain invariant: variable-bodied λs stay variable-bodied).

## The resolution — trust the classifier (brick 7)

The λ arm no longer compares annotations: it EMITS the classifier's domain and descends
unconditionally, so outputs are annotation-canonical.  Soundness re-types the body across the
binder via the grown EXACT context conversion (`contextConversionExact` over the
replaced-entry `ConvContextWithOldValid` — `invertLam` + Π-code injectivity supply
`Conv domainAnn domainCode`, the wf lookups validate the old entries), and the congruence
witness routes by `trans` through the annotation-canonicalized λ.  Both λs now read back to the
η-long `λ(Unit).unit` at fuel 1 (`readback_canonicalizesAnnotations`, `rfl`) and
`ofReadbackEqual` decides the pair (`annotationPair_decidedByReadback`).

## What this boundary was — and was not

The PAIR was always decidable by the shipped βη machinery (`annotationLambdas_oneStepApart`:
one congruence step joins them; the `Cong` witness IS `ofBetaEtaConv`).  What the boundary
exposed was the READBACK as a canonicalizer: pre-fix, a normalize-and-compare decider (#364)
computed distinct never-joining forms for definitionally equal, identically-classified
subjects.  CANONICAL-FORM completeness, not pair-decidability.

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

/-- **The trust-the-classifier λ arm canonicalizes the annotation (brick 7)**: at every positive
fuel the redex-annotated λ reads back to the η-long `λ(Unit).unit` — the emitted binder carries
the CLASSIFIER's domain, and under `cons Unit` the body variable's looked-up classifier is the
literal unit code, so the unit collapse fires. -/
theorem readback_annotatedByRedex_isEtaLong (profile : PolyProfile) :
    ∀ fuel : Nat,
      readbackAtClassifier (fuel + 1) (TypingContext.empty : TypingContext profile 0)
          (piTyCodeCell unitTypeCell unitTypeCell) annotatedByRedex
        = lamCell unitTypeCell unitCell
  | 0 => rfl
  | _ + 1 => rfl

/-- The DEEP COLLAPSE stays blind: under `cons redexAnnotation` the body variable's looked-up
classifier is the weakened REDEX, not the literal unit code, so the collapse fixes the
redex-annotated λ — unit-typedness hides BEHIND the redex. -/
theorem deepCollapse_annotatedByRedex (profile : PolyProfile) :
    collapseUnitVariablesDeep (TypingContext.empty : TypingContext profile 0) annotatedByRedex
      = annotatedByRedex := rfl

theorem deepCollapse_annotatedByLiteral (profile : PolyProfile) :
    collapseUnitVariablesDeep (TypingContext.empty : TypingContext profile 0) annotatedByLiteral
      = lamCell unitTypeCell unitCell := rfl

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

/-- **The deep-collapse outputs never βη-join**: every reduct of the collapse-fixed
redex-annotated λ keeps its VARIABLE body, while the η-long form's body is the `unit` value —
and the η-long form is βη-normal, so any common reduct must BE it. -/
theorem annotationCollapseForms_notBetaEtaConv :
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
    Bool.false_ne_true

/-- **★ The 9th boundary, against the FROZEN deep-collapse ingredient**: a pair of λ-terms BOTH
grown-typed at the same formation-typed classifier `Π(_:Unit).Unit` in the wf empty context,
congruently unit-η-equal (indeed βη-equal in one congruence step), whose DEEP COLLAPSES are
distinct never-βη-joining forms — the collapse's syntactic lookup test cannot see
unit-typedness behind a redex annotation.  This boundary FORCED the trust-the-classifier λ arm
(brick 7), which decides the pair below. -/
theorem deepCollapseMode_isIncompleteAtAnnotationMismatch (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 0),
      DefEqUnitEtaCong profile (TypingContext.empty : TypingContext profile 0)
        leftTerm rightTerm ∧
      HasTypeDescPi profile TypingContext.empty leftTerm
        (piTyCodeCell unitTypeCell unitTypeCell) ∧
      HasTypeDescPi profile TypingContext.empty rightTerm
        (piTyCodeCell unitTypeCell unitTypeCell) ∧
      collapseUnitVariablesDeep (TypingContext.empty : TypingContext profile 0) leftTerm
        ≠ collapseUnitVariablesDeep (TypingContext.empty : TypingContext profile 0) rightTerm ∧
      ¬ BetaEtaConv
        (collapseUnitVariablesDeep (TypingContext.empty : TypingContext profile 0) leftTerm)
        (collapseUnitVariablesDeep (TypingContext.empty : TypingContext profile 0) rightTerm) :=
  ⟨annotatedByRedex, annotatedByLiteral,
    annotationPair_congruentlyEqual profile,
    annotatedByRedexTyped profile,
    annotatedByLiteralTyped profile,
    fun collapsesEqual =>
      absurd
        (show annotatedByRedex = lamCell unitTypeCell unitCell from collapsesEqual)
        (by decide),
    fun convertible => annotationCollapseForms_notBetaEtaConv convertible⟩

/-- **★ The annotation-canonical readback identifies the pair (brick-7 payoff)**: at fuel 1
both λs read back to the same η-long `λ(Unit).unit` — the emitted annotation comes from the
classifier, by `rfl`. -/
theorem readback_canonicalizesAnnotations (profile : PolyProfile) :
    readbackAtClassifier 1 (TypingContext.empty : TypingContext profile 0)
        (piTyCodeCell unitTypeCell unitTypeCell) annotatedByRedex
      = readbackAtClassifier 1 (TypingContext.empty : TypingContext profile 0)
          (piTyCodeCell unitTypeCell unitTypeCell) annotatedByLiteral := rfl

/-- **★ THE 9TH-BOUNDARY PAIR, DECIDED — `ofReadbackEqual` now closes it at `rfl`**: both
endpoints typed at the formation-typed classifier, wf empty context, equal readbacks at
fuel 1. -/
theorem annotationPair_decidedByReadback (profile : PolyProfile) :
    DefEqUnitEtaCong profile (TypingContext.empty : TypingContext profile 0)
      annotatedByRedex annotatedByLiteral :=
  DefEqUnitEtaCong.ofReadbackEqual (leftFuel := 1) (rightFuel := 1)
    WfContextDesc.emptyIsWellFormed
    (annotatedByRedexTyped profile)
    (annotatedByLiteralTyped profile)
    (hasTypeDesc_piFormation_viaGenArm TypingContext.empty
      unitTypeCell unitTypeCell LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
      (unitTypeCellFormationTyped TypingContext.empty)
      (unitTypeCellFormationTyped (TypingContext.empty.cons unitTypeCell)))
    rfl

end FX1Poly.Typed
