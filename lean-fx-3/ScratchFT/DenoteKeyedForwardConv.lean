import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Core.StratifiedReducibleTypeConvInvariance

/-! Scratch: forward closure + conversion-invariance for the denote-keyed relation, ported from
StratifiedReducibleTypeForwardClosure / ConvInvariance. The helpers (commuteWithStep,
weakHeadNormalRootStableAlongStepStar, piTyCode_decompose, subst0Body, eq_of_noStep, noStep_universeCode)
are relation-agnostic, reused verbatim; only the reducibility constructors change to the denote-keyed ones.
Probe: all zero-axiom. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- Forward closure of a denote-keyed whnfExpand code along StepStar (port of whnfExpandClosure). -/
theorem ReducibleTypeStepDenote.whnfExpandClosure {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {candidate : RawTerm scope → Prop} :
    ∀ {firstType finalType : RawTerm scope}, StepStar firstType finalType →
      ∀ {weakHeadReduct : RawTerm scope}, WeakHeadStep firstType weakHeadReduct →
        ReducibleTypeStepDenote env lowerAt weakHeadReduct candidate →
        (∀ furtherReduct : RawTerm scope, StepStar weakHeadReduct furtherReduct →
          ReducibleTypeStepDenote env lowerAt furtherReduct candidate) →
        ReducibleTypeStepDenote env lowerAt finalType candidate := by
  intro firstType finalType chain
  induction chain with
  | refl _ =>
      intro weakHeadReduct weakHeadStep reductReducible _laterClosure
      exact ReducibleTypeStepDenote.whnfExpand weakHeadStep reductReducible
  | trans firstStep _restChain restClosure =>
      intro weakHeadReduct weakHeadStep reductReducible laterClosure
      rcases weakHeadStep.commuteWithStep _ firstStep with
        midEquation | ⟨_laterReduct, laterWeakHeadStep, catchUpChain⟩
      · subst midEquation
        exact laterClosure _ _restChain
      · exact restClosure laterWeakHeadStep (laterClosure _ catchUpChain)
          (fun furtherReduct furtherChain =>
            laterClosure furtherReduct (StepStar.trans_compose catchUpChain furtherChain))

/-- Forward closure of the denote-keyed reducibility relation under StepStar (port of forwardStepStar). -/
theorem ReducibleTypeStepDenote.forwardStepStar {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {candidate : RawTerm scope → Prop} {typeCode : RawTerm scope}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {finalType : RawTerm scope}, StepStar typeCode finalType →
      ReducibleTypeStepDenote env lowerAt finalType candidate := by
  induction reducible with
  | whnfExpand weakHeadStep reductReducible reductInductiveHypothesis =>
      intro finalType chain
      exact ReducibleTypeStepDenote.whnfExpandClosure chain weakHeadStep reductReducible
        (fun _furtherReduct furtherChain => reductInductiveHypothesis furtherChain)
  | neutral noWeakHeadStep notPiType notUniverse =>
      intro finalType chain
      obtain ⟨finalNoWeakHeadStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain noWeakHeadStep
      exact ReducibleTypeStepDenote.neutral finalNoWeakHeadStep
        (fun rootIsPiType => notPiType (rootEquation.symm.trans rootIsPiType))
        (fun rootIsUniverse => notUniverse (rootEquation.symm.trans rootIsUniverse))
  | piType codomainCandidate _domainReducible _codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro finalType chain
      obtain ⟨_updatedDomain, _updatedCodomain, finalEquation, domainChain, codomainChain⟩ :=
        StepStar.piTyCode_decompose chain
      subst finalEquation
      exact ReducibleTypeStepDenote.piType codomainCandidate (domainInductiveHypothesis domainChain)
        (fun argument domainMember =>
          codomainInductiveHypothesis argument domainMember
            (StepStar.subst0Body argument codomainChain))
  | universeCode levelExpr flag =>
      intro finalType chain
      have finalEquation :=
        StepStar.eq_of_noStep (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step)
          chain
      subst finalEquation
      exact ReducibleTypeStepDenote.universeCode levelExpr flag
  | ofPointwiseIff _innerReducible pointwiseIff innerHypothesis =>
      intro finalType chain
      exact (innerHypothesis chain).ofPointwiseIff pointwiseIff

/-- Forward closure, level-indexed (direct — no Nat recursion). -/
theorem ReducibleTypeAtDenote.forwardStepStar {scope : Nat} {env : Nat → Nat} {level : Nat}
    {candidate : RawTerm scope → Prop} {typeCode finalType : RawTerm scope}
    (reducible : ReducibleTypeAtDenote env level typeCode candidate)
    (chain : StepStar typeCode finalType) :
    ReducibleTypeAtDenote env level finalType candidate :=
  ReducibleTypeStepDenote.forwardStepStar reducible chain

/-- Conversion-invariance of the denote-keyed relation (port of convInvariant). -/
theorem ReducibleTypeStepDenote.convInvariant {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeStepDenote env lowerAt typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeStepDenote env lowerAt typeRight candidateRight)
    (conv : Conv typeLeft typeRight) :
    PointwiseIff candidateLeft candidateRight := by
  obtain ⟨_commonReduct, chainLeft, chainRight⟩ := conv
  exact ReducibleTypeStepDenote.deterministic
    (ReducibleTypeStepDenote.forwardStepStar reducibleLeft chainLeft)
    (ReducibleTypeStepDenote.forwardStepStar reducibleRight chainRight)

/-- Reducibility transfers across conversion (denote-keyed). -/
theorem ReducibleTypeStepDenote.convTransfer {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeStepDenote env lowerAt typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeStepDenote env lowerAt typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  (ReducibleTypeStepDenote.convInvariant reducibleLeft reducibleRight conv term).mp membership

/-- Conversion-transfer, level-indexed. -/
theorem ReducibleTypeAtDenote.convTransfer {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeAtDenote env level typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeAtDenote env level typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  ReducibleTypeStepDenote.convTransfer reducibleLeft reducibleRight conv membership

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.whnfExpandClosure
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.forwardStepStar
#print axioms FX1Poly.Typed.ReducibleTypeAtDenote.forwardStepStar
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.convInvariant
#print axioms FX1Poly.Typed.ReducibleTypeStepDenote.convTransfer
#print axioms FX1Poly.Typed.ReducibleTypeAtDenote.convTransfer
