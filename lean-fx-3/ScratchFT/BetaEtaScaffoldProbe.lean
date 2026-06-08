import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.StrongNormalizationEta

/-! Probe (NEVER committed): OSN-1 scaffolding — name the precise crux + the complete pieces it enables.
    Full βη-SN (union) needs η-postponement over β (β/η interleave; no single measure decreases on both;
    constructive SN-of-union needs lex/ordinal-rank infra not in Init). This file ships the COMPLETE,
    non-vacuous pieces: (1) the crux predicate, (2) well-typed ⇒ β-SN ∧ η-SN separately, (3) crux ⇒
    η-reducts of well-typed terms stay β-SN. -/

namespace FX1Poly.Typed.Spike

open FX1Poly.Core

/-- The precise remaining crux for βη-SN: η-reducts of β-SN terms are β-SN. -/
def EtaPreservesBetaStronglyNormalizing : Prop :=
  ∀ {scope : Nat} {sourceTerm targetTerm : RawTerm scope},
    Step.eta sourceTerm targetTerm →
    StepStar.IsStronglyNormalizing sourceTerm →
    StepStar.IsStronglyNormalizing targetTerm

/-- Well-typed open terms are strongly normalizing under β (OB-5) AND under η (unconditional), separately. -/
theorem componentwiseStronglyNormalizing {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject ∧ Step.etaStar.IsStronglyNormalizing subject :=
  ⟨HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed,
   Step.etaStar.isStronglyNormalizing subject⟩

/-- Given the crux, η-reducts of well-typed open terms remain β-strongly-normalizing. -/
theorem etaReductOfWellTypedIsBetaStronglyNormalizing
    (etaPreserves : EtaPreservesBetaStronglyNormalizing)
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier reduct : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    (etaStep : Step.eta subject reduct) :
    StepStar.IsStronglyNormalizing reduct :=
  etaPreserves etaStep (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed)

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.componentwiseStronglyNormalizing
#print axioms FX1Poly.Typed.Spike.etaReductOfWellTypedIsBetaStronglyNormalizing
