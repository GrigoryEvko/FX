import FX1Poly.Typed.DenoteKeyedUniformReducible

/-! Scratch (#752 backbone induction): the level-irrelevance induction over `ReducibleTypeStepDenote` with the
STRONGER `UniformlyReducibleAboveDenote` motive, piType isolated as the `piArm` hypothesis.  Verbatim mirror of
the shipped all-levels `IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote` — same 5-arm dispatch
(whnfExpand→headExpand, neutral→ofNeutral, universeCode→ofUniverseCode, ofPointwiseIff→IH, piType→piArm), only
the motive and the three leaf lemmas swapped to the uniform-above-threshold versions.  Probing zero-axiom. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem UniformlyReducibleAboveDenote.ofReducibleTypeStepDenote {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) →
        UniformlyReducibleAboveDenote env domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          UniformlyReducibleAboveDenote env (RawTerm.subst0 codomainCode argument)) →
        UniformlyReducibleAboveDenote env
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    UniformlyReducibleAboveDenote env typeCode := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact UniformlyReducibleAboveDenote.headExpand weakHeadStep reductInductiveHypothesis
  | neutral noWeakHeadStep notPiType notUniverse =>
      exact UniformlyReducibleAboveDenote.ofNeutral noWeakHeadStep notPiType notUniverse
  | @piType domainCode codomainCode domainCandidate codomainCandidate domainReducible
      codomainReducible domainInductiveHypothesis codomainInductiveHypothesis =>
      exact piArm codomainCandidate domainReducible codomainReducible
        domainInductiveHypothesis codomainInductiveHypothesis
  | universeCode levelExpr flag =>
      exact UniformlyReducibleAboveDenote.ofUniverseCode env levelExpr flag
  | ofPointwiseIff _innerReducible _pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis

end FX1Poly.Typed

#print axioms FX1Poly.Typed.UniformlyReducibleAboveDenote.ofReducibleTypeStepDenote
