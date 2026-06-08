import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.UniverseCodeShape

/-! Scratch probe: port the CR machinery (shape inversions + determinism) onto ReducibleTypeStepDenote,
mirroring StratifiedReducibleType. The only structural difference from the fuel version: the universe arm's
candidate depends on levelExpr (universeDenotePredicate env lowerAt levelExpr), so candidateIffUniverse /
deterministic use universeCodeCell_inj to align the levelExpr. Probe: all zero-axiom. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- Weak-head peel through ofPointwiseIff (denote-keyed). -/
theorem ReducibleTypeStepDenote.candidateAtWhnfReduct {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {reduct : RawTerm scope}, WeakHeadStep typeCode reduct →
      ReducibleTypeStepDenote env lowerAt reduct candidate := by
  induction reducible with
  | whnfExpand weakHeadStep0 reductReducible0 _ =>
      intro reduct weakHeadStep
      have reductEquation := WeakHeadStep.deterministic weakHeadStep0 weakHeadStep
      subst reductEquation
      exact reductReducible0
  | neutral noWeakHeadStep _ _ =>
      intro reduct weakHeadStep
      exact absurd weakHeadStep (noWeakHeadStep reduct)
  | piType _ _ _ _ _ =>
      intro reduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | universeCode _ _ =>
      intro reduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro reduct weakHeadStep
      exact .ofPointwiseIff (innerHypothesis weakHeadStep) pointwiseIff

/-- A weak-head-normal non-Π non-universe type has the SN candidate (denote-keyed). -/
theorem ReducibleTypeStepDenote.candidateIffStronglyNormalizing {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    (∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct) →
    typeCode.rootGenerator ≠ Generator.gen_piTyCode →
    typeCode.rootGenerator ≠ Generator.gen_universeCode →
    PointwiseIff candidate IsStronglyNormalizing := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro noWeakHeadStep _ _; exact absurd weakHeadStep0 (noWeakHeadStep _)
  | neutral _ _ _ => intro _ _ _ _term; exact Iff.rfl
  | piType _ _ _ _ _ => intro _ notPiType _; exact absurd rfl notPiType
  | universeCode _ _ => intro _ _ notUniverse; exact absurd rfl notUniverse
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro noWeakHeadStep notPiType notUniverse term
      exact (pointwiseIff term).symm.trans (innerHypothesis noWeakHeadStep notPiType notUniverse term)

/-- Π-shape inversion (denote-keyed, subject generic + equation). -/
theorem ReducibleTypeStepDenote.candidatePiShape {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
      typeCode = (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) →
      ∃ (domainCandidate : RawTerm scope → Prop)
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate ∧
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) ∧
        PointwiseIff candidate
          (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _domainCode _codomainCode hType; subst hType
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | neutral _ notPiType _ =>
      intro _domainCode _codomainCode hType; subst hType; exact absurd rfl notPiType
  | piType codomainCandidate domainReducible codomainReducible _ _ =>
      intro _domainCode _codomainCode hType; cases hType
      exact ⟨_, codomainCandidate, domainReducible, codomainReducible, fun _term => Iff.rfl⟩
  | universeCode _ _ =>
      intro _domainCode _codomainCode hType
      have rootMismatch : Generator.gen_universeCode = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch (by decide)
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _domainCode _codomainCode hType
      obtain ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible, pwi⟩ :=
        innerHypothesis hType
      exact ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible,
        fun term => (pointwiseIff term).symm.trans (pwi term)⟩

/-- Universe-shape inversion (denote-keyed): aligns the levelExpr via universeCodeCell_inj. -/
theorem ReducibleTypeStepDenote.candidateIffUniverse {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {levelExpr : LevelExpr} {flag : UniverseFlag},
      typeCode = (.mkGen .gen_universeCode (levelExpr, flag) .childNil) →
      PointwiseIff candidate (universeDenotePredicate env lowerAt levelExpr) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _levelExpr _flag hType; subst hType
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | neutral _ _ notUniverse =>
      intro _levelExpr _flag hType; subst hType; exact absurd rfl notUniverse
  | piType _ _ _ _ _ =>
      intro _levelExpr _flag hType
      have rootMismatch : Generator.gen_piTyCode = Generator.gen_universeCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch (by decide)
  | universeCode levelExpr flag =>
      intro _levelExpr _flag hType term
      obtain ⟨levelEq, _flagEq⟩ := universeCodeCell_inj hType
      subst levelEq
      exact Iff.rfl
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _levelExpr _flag hType term
      exact (pointwiseIff term).symm.trans (innerHypothesis hType term)

/-- The denote-keyed step functor is functional up to pointwise iff. -/
theorem ReducibleTypeStepDenote.deterministic {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate1 : RawTerm scope → Prop}
    (reducible1 : ReducibleTypeStepDenote env lowerAt typeCode candidate1) :
    ∀ {candidate2 : RawTerm scope → Prop},
      ReducibleTypeStepDenote env lowerAt typeCode candidate2 → PointwiseIff candidate1 candidate2 := by
  induction reducible1 with
  | whnfExpand weakHeadStep1 _reductReducible1 reductInductiveHypothesis =>
      intro candidate2 reducible2
      exact reductInductiveHypothesis (reducible2.candidateAtWhnfReduct weakHeadStep1)
  | neutral noWeakHeadStep1 notPiType1 notUniverse1 =>
      intro candidate2 reducible2 term
      exact (reducible2.candidateIffStronglyNormalizing noWeakHeadStep1 notPiType1 notUniverse1 term).symm
  | piType codomainCandidate1 _domainReducible1 _codomainReducible1
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro candidate2 reducible2
      obtain ⟨domainCandidate2, codomainCandidate2, _domainReducible2, codomainReducible2, pointwiseIff2⟩ :=
        reducible2.candidatePiShape rfl
      refine fun functionTerm => Iff.trans ?_ (pointwiseIff2 functionTerm).symm
      constructor
      · intro membership1 argument domain2Argument
        have domain1Argument := (domainInductiveHypothesis _domainReducible2 argument).mpr domain2Argument
        have codomainEquivalence :=
          codomainInductiveHypothesis argument domain1Argument
            (codomainReducible2 argument domain2Argument)
        exact (codomainEquivalence _).mp (membership1 argument domain1Argument)
      · intro membership2 argument domain1Argument
        have domain2Argument := (domainInductiveHypothesis _domainReducible2 argument).mp domain1Argument
        have codomainEquivalence :=
          codomainInductiveHypothesis argument domain1Argument
            (codomainReducible2 argument domain2Argument)
        exact (codomainEquivalence _).mpr (membership2 argument domain2Argument)
  | universeCode _levelExpr1 _flag1 =>
      intro candidate2 reducible2 term
      exact (reducible2.candidateIffUniverse rfl term).symm
  | ofPointwiseIff _innerReducible1 pointwiseIff1 innerInductiveHypothesis1 =>
      intro candidate2 reducible2 term
      exact (pointwiseIff1 term).symm.trans (innerInductiveHypothesis1 reducible2 term)

/-- Π-code inversion (existential, denote-keyed): a Π-rooted reducible type came through the piType arm. -/
theorem ReducibleTypeAtDenote.piTypeInversion {scope : Nat} {env : Nat → Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) candidate) :
    ∃ (domainCandidate : RawTerm scope → Prop)
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
      ReducibleTypeAtDenote env level domainCode domainCandidate ∧
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) ∧
      PointwiseIff candidate
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  reducible.candidatePiShape rfl

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateAtWhnfReduct
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateIffStronglyNormalizing
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidatePiShape
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.candidateIffUniverse
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.deterministic
#print axioms FX1Poly.Typed.ReducibleTypeAtDenote.piTypeInversion
