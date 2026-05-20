import LeanFX2.Term

/-! # Term/HEqCongr/Atomic/HeterogeneousIntro

Heterogeneous HoTT introduction HEq congruences. -/

namespace LeanFX2

/-- HEq congruence for heterogeneous equivalence introduction. -/
theorem Term.equivIntroHet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {forwardRaw1 forwardRaw2 backwardRaw1 backwardRaw2 : RawTerm scope}
    {leftInvRaw1 leftInvRaw2 rightInvRaw1 rightInvRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (forwardRawEq : forwardRaw1 = forwardRaw2)
    (backwardRawEq : backwardRaw1 = backwardRaw2)
    (leftInvRawEq : leftInvRaw1 = leftInvRaw2)
    (rightInvRawEq : rightInvRaw1 = rightInvRaw2)
    {forward1 : Term context (Ty.arrow carrierA1 carrierB1) forwardRaw1}
    {forward2 : Term context (Ty.arrow carrierA2 carrierB2) forwardRaw2}
    (forwardHEq : HEq forward1 forward2)
    {backward1 : Term context (Ty.arrow carrierB1 carrierA1) backwardRaw1}
    {backward2 : Term context (Ty.arrow carrierB2 carrierA2) backwardRaw2}
    (backwardHEq : HEq backward1 backward2)
    {leftInv1 :
      Term context
        (equivIntroHetLeftInverseType carrierA1 forwardRaw1 backwardRaw1)
        leftInvRaw1}
    {leftInv2 :
      Term context
        (equivIntroHetLeftInverseType carrierA2 forwardRaw2 backwardRaw2)
        leftInvRaw2}
    (leftInvHEq : HEq leftInv1 leftInv2)
    {rightInv1 :
      Term context
        (equivIntroHetRightInverseType carrierB1 forwardRaw1 backwardRaw1)
        rightInvRaw1}
    {rightInv2 :
      Term context
        (equivIntroHetRightInverseType carrierB2 forwardRaw2 backwardRaw2)
        rightInvRaw2}
    (rightInvHEq : HEq rightInv1 rightInv2) :
    HEq (Term.equivIntroHet forward1 backward1 leftInv1 rightInv1)
      (Term.equivIntroHet forward2 backward2 leftInv2 rightInv2) := by
  subst carrierAEq
  subst carrierBEq
  subst forwardRawEq
  subst backwardRawEq
  subst leftInvRawEq
  subst rightInvRawEq
  cases forwardHEq
  cases backwardHEq
  cases leftInvHEq
  cases rightInvHEq
  rfl

/-- HEq congruence for heterogeneous univalence introduction. -/
theorem Term.uaIntroHet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {carrierARaw1 carrierARaw2 carrierBRaw1 carrierBRaw2 : RawTerm scope}
    {forwardRaw1 forwardRaw2 backwardRaw1 backwardRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (carrierARawEq : carrierARaw1 = carrierARaw2)
    (carrierBRawEq : carrierBRaw1 = carrierBRaw2)
    (forwardRawEq : forwardRaw1 = forwardRaw2)
    (backwardRawEq : backwardRaw1 = backwardRaw2)
    {equivWitness1 :
      Term context (Ty.equiv carrierA1 carrierB1)
        (RawTerm.equivIntro forwardRaw1 backwardRaw1)}
    {equivWitness2 :
      Term context (Ty.equiv carrierA2 carrierB2)
        (RawTerm.equivIntro forwardRaw2 backwardRaw2)}
    (equivWitnessHEq : HEq equivWitness1 equivWitness2) :
    HEq
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw1 carrierBRaw1
        equivWitness1)
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw2 carrierBRaw2
        equivWitness2) := by
  subst carrierAEq
  subst carrierBEq
  subst carrierARawEq
  subst carrierBRawEq
  subst forwardRawEq
  subst backwardRawEq
  cases equivWitnessHEq
  rfl

/-- HEq congruence for heterogeneous funext introduction. -/
theorem Term.funextIntroHet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {applyARaw1 applyARaw2 applyBRaw1 applyBRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (applyARawEq : applyARaw1 = applyARaw2)
    (applyBRawEq : applyBRaw1 = applyBRaw2) :
    HEq
      (Term.funextIntroHet (context := context) domainType1 codomainType1
        applyARaw1 applyBRaw1)
      (Term.funextIntroHet (context := context) domainType2 codomainType2
        applyARaw2 applyBRaw2) := by
  subst domainEq
  subst codomainEq
  subst applyARawEq
  subst applyBRawEq
  rfl

end LeanFX2
