import FX1Poly.Typed.TypedChurchNumeralMultiplication

namespace FX1Poly.Typed
open FX1Poly.Core

-- Clean expression abbreviations (definitionally equal to the shipped theorem LHSs).
def churchNumeralApplied (count : Nat) (typeA handlerF baseX : RawTerm 0) : RawTerm 0 :=
  appCell (appCell (appCell (churchNumeralLambda count) typeA) handlerF) baseX

def churchAdditionBody (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) : RawTerm 0 :=
  appCell (appCell (appCell (churchNumeralLambda countLeft) typeA) handlerF)
    (appCell (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF) baseX)

def churchMultiplicationBody (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) : RawTerm 0 :=
  appCell (appCell (appCell (churchNumeralLambda countLeft) typeA)
    (appCell (appCell (churchNumeralLambda countRight) typeA) handlerF)) baseX

-- Addition commutativity.
theorem churchAdditionCommutes (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchAdditionBody countLeft countRight typeA handlerF baseX)
      (churchAdditionBody countRight countLeft typeA handlerF baseX) :=
  ⟨iteratedApplication (countLeft + countRight) handlerF baseX,
   churchAdditionBodyComputes countLeft countRight typeA handlerF baseX,
   Nat.add_comm countRight countLeft ▸ churchAdditionBodyComputes countRight countLeft typeA handlerF baseX⟩

-- Addition associativity.
theorem churchAdditionAssociates (countLeft countMiddle countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    Conv (churchAdditionBody (countLeft + countMiddle) countRight typeA handlerF baseX)
      (churchAdditionBody countLeft (countMiddle + countRight) typeA handlerF baseX) :=
  ⟨iteratedApplication ((countLeft + countMiddle) + countRight) handlerF baseX,
   churchAdditionBodyComputes (countLeft + countMiddle) countRight typeA handlerF baseX,
   Nat.add_assoc countLeft countMiddle countRight ▸
     churchAdditionBodyComputes countLeft (countMiddle + countRight) typeA handlerF baseX⟩

-- Zero is the additive identity.
theorem churchAddZeroIsIdentity (count : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchAdditionBody count 0 typeA handlerF baseX)
      (churchNumeralApplied count typeA handlerF baseX) :=
  ⟨iteratedApplication count handlerF baseX,
   churchAdditionBodyComputes count 0 typeA handlerF baseX,
   churchNumeral_appliedReducesToIterate_general count typeA handlerF baseX⟩

-- Multiplication commutativity.
theorem churchMultiplicationCommutes (countLeft countRight : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody countLeft countRight typeA handlerF baseX)
      (churchMultiplicationBody countRight countLeft typeA handlerF baseX) :=
  ⟨iteratedApplication (countLeft * countRight) handlerF baseX,
   churchMultiplicationBodyComputes countLeft countRight typeA handlerF baseX,
   Nat.mul_comm countRight countLeft ▸
     churchMultiplicationBodyComputes countRight countLeft typeA handlerF baseX⟩

-- One is the multiplicative identity.
theorem churchMulOneIsIdentity (count : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody count 1 typeA handlerF baseX)
      (churchNumeralApplied count typeA handlerF baseX) := by
  have indexEq : iteratedApplication (count * 1) handlerF baseX
      = iteratedApplication count handlerF baseX := by rw [Nat.mul_one]
  exact ⟨iteratedApplication (count * 1) handlerF baseX,
    churchMultiplicationBodyComputes count 1 typeA handlerF baseX,
    indexEq.symm ▸ churchNumeral_appliedReducesToIterate_general count typeA handlerF baseX⟩

-- Zero annihilates under multiplication.
theorem churchMulZeroAnnihilates (count : Nat) (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody count 0 typeA handlerF baseX)
      (churchNumeralApplied 0 typeA handlerF baseX) :=
  ⟨iteratedApplication 0 handlerF baseX,
   churchMultiplicationBodyComputes count 0 typeA handlerF baseX,
   churchNumeral_appliedReducesToIterate_general 0 typeA handlerF baseX⟩

-- Left distributivity: m * (n + p) = m*n + m*p.
theorem churchMultiplicationDistributesOverAddition (countLeft countMiddle countRight : Nat)
    (typeA handlerF baseX : RawTerm 0) :
    Conv (churchMultiplicationBody countLeft (countMiddle + countRight) typeA handlerF baseX)
      (churchAdditionBody (countLeft * countMiddle) (countLeft * countRight) typeA handlerF baseX) :=
  ⟨iteratedApplication (countLeft * (countMiddle + countRight)) handlerF baseX,
   churchMultiplicationBodyComputes countLeft (countMiddle + countRight) typeA handlerF baseX,
   (Nat.mul_add countLeft countMiddle countRight).symm ▸
     churchAdditionBodyComputes (countLeft * countMiddle) (countLeft * countRight) typeA handlerF baseX⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.churchAdditionCommutes
#print axioms FX1Poly.Typed.churchAdditionAssociates
#print axioms FX1Poly.Typed.churchAddZeroIsIdentity
#print axioms FX1Poly.Typed.churchMultiplicationCommutes
#print axioms FX1Poly.Typed.churchMulOneIsIdentity
#print axioms FX1Poly.Typed.churchMulZeroAnnihilates
#print axioms FX1Poly.Typed.churchMultiplicationDistributesOverAddition
