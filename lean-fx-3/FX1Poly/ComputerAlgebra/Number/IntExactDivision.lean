import FX1Poly.ComputerAlgebra.Number.IntCancellation
import FX1Poly.ComputerAlgebra.Number.IntNegation
import FX1Poly.ComputerAlgebra.Number.IntOrderAlgebra
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision

/-! # FX1Poly/ComputerAlgebra/Number/IntExactDivision — sign-aware exact division
    (FLOAT-2 brick 5a)

Radix normalization divides the mantissa by the radix exactly for as long as it can.
The counting divider works on `Nat`, so this module reattaches the sign: divide the
MAGNITUDE of an `Int` by a `Nat` divisor, and when the remainder vanishes the
factorization `mantissa = quotient * divisor` holds in `Int` — the ONLY fact the
normalization loop rewrites by.

  * `intMagnitudeRemainder` / `intMagnitudeQuotient` — the counting division of the
    magnitude, quotient sign-reattached.
  * `intMagnitudeDivisionExact` — a vanishing remainder yields the exact `Int`
    factorization (per-constructor: `ofNat` is one `congrArg Int.ofNat`, `negSucc`
    rides `intNegMul` through the definitional `-(Int.ofNat (n + 1)) = negSucc n`).
  * `intOfNatToNatOfNonNeg` — `Int.ofNat value.toNat = value` on nonnegative values,
    the round-trip that lets a positive `Int` radix feed the `Nat` divider.

## Zero-axiom

Constructor matches + `congrArg`/`Eq.trans` chains over the counting-divider
certificates.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Number/IntExactDivision.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-- The remainder of dividing an `Int`'s MAGNITUDE by a `Nat` divisor. -/
def intMagnitudeRemainder (divisor : Nat) : Int → Nat
  | .ofNat magnitude => (natDivModCounting magnitude divisor).snd
  | .negSucc magnitudePredecessor =>
      (natDivModCounting (magnitudePredecessor + 1) divisor).snd

/-- The quotient of dividing an `Int`'s MAGNITUDE by a `Nat` divisor, with the sign
reattached.  Meaningful as an exact quotient only when `intMagnitudeRemainder`
vanishes — the only situation the normalization loop uses it in. -/
def intMagnitudeQuotient (divisor : Nat) : Int → Int
  | .ofNat magnitude => Int.ofNat (natDivModCounting magnitude divisor).fst
  | .negSucc magnitudePredecessor =>
      -(Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).fst)

/-- **Exactness**: a vanishing magnitude remainder yields the `Int` factorization
`mantissa = quotient * divisor`.  Both arms run the counting-divider reconstruction
into the zero remainder (`x + 0` is definitional) and flip the factor order; the
`negSucc` arm additionally pulls the sign out through `intNegMul`. -/
theorem intMagnitudeDivisionExact (divisor : Nat) : ∀ mantissa : Int,
    intMagnitudeRemainder divisor mantissa = 0 →
    mantissa = intMagnitudeQuotient divisor mantissa * Int.ofNat divisor
  | .ofNat magnitude, hasZeroRemainder =>
      congrArg Int.ofNat
        ((natDivModCountingReconstructs magnitude divisor).trans
          ((congrArg
              (divisor * (natDivModCounting magnitude divisor).fst + ·)
              hasZeroRemainder).trans
            (Nat.mul_comm divisor (natDivModCounting magnitude divisor).fst)))
  | .negSucc magnitudePredecessor, hasZeroRemainder =>
      (congrArg (fun magnitudeValue => -(Int.ofNat magnitudeValue))
          ((natDivModCountingReconstructs (magnitudePredecessor + 1) divisor).trans
            ((congrArg
                (divisor *
                  (natDivModCounting (magnitudePredecessor + 1) divisor).fst + ·)
                hasZeroRemainder).trans
              (Nat.mul_comm divisor
                (natDivModCounting (magnitudePredecessor + 1) divisor).fst)))).trans
        (intNegMul
          (Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).fst)
          (Int.ofNat divisor)).symm

/-- `Int.ofNat value.toNat = value` on nonnegative values — the round-trip that feeds
a positive `Int` radix into the `Nat` divider and back. -/
theorem intOfNatToNatOfNonNeg {value : Int} (isNonNegative : (0 : Int) ≤ value) :
    Int.ofNat value.toNat = value :=
  match intZeroLeDest isNonNegative with
  | ⟨_, valueEquation⟩ =>
      (congrArg (fun sameValue => Int.ofNat sameValue.toNat) valueEquation).trans
        valueEquation.symm

/-! ## The magnitude bridges — `natAbs` plumbing for the normalization fuel bound -/

/-- Negating an `ofNat` keeps the magnitude — both `Int.negOfNat` arms are `rfl`. -/
theorem intNegOfNatNatAbs : ∀ magnitude : Nat, (-(Int.ofNat magnitude)).natAbs = magnitude
  | 0 => rfl
  | _ + 1 => rfl

/-- The magnitude remainder IS the counting divider's remainder at `natAbs` — both
constructor arms are `rfl`; this lets abstract-mantissa reasoning reuse the divider
certificates. -/
theorem intMagnitudeRemainderAsCounting (divisor : Nat) : ∀ mantissa : Int,
    intMagnitudeRemainder divisor mantissa =
      (natDivModCounting mantissa.natAbs divisor).snd
  | .ofNat _ => rfl
  | .negSucc _ => rfl

/-- The magnitude quotient's magnitude IS the counting divider's quotient at `natAbs`
— the `negSucc` arm rides the sign-stripping `intNegOfNatNatAbs`. -/
theorem intMagnitudeQuotientNatAbs (divisor : Nat) : ∀ mantissa : Int,
    (intMagnitudeQuotient divisor mantissa).natAbs =
      (natDivModCounting mantissa.natAbs divisor).fst
  | .ofNat _ => rfl
  | .negSucc magnitudePredecessor =>
      intNegOfNatNatAbs
        (natDivModCounting (magnitudePredecessor + 1) divisor).fst

/-- A vanishing magnitude is a vanishing integer — `negSucc` magnitudes are successors,
so only `ofNat 0` survives. -/
theorem intEqZeroOfNatAbsEqZero : ∀ {value : Int}, value.natAbs = 0 → value = 0
  | .ofNat _, hasZeroNatAbs => congrArg Int.ofNat hasZeroNatAbs
  | .negSucc _, hasZeroNatAbs => Nat.noConfusion hasZeroNatAbs

/-- A radix above `1` has magnitude at least `2` — destruct the (definitionally
`2 ≤ radix`) bound to an additive witness and read the `toNat` off it. -/
theorem intToNatAtLeastTwoOfOneLessThan {radix : Int}
    (isRadixAboveOne : (1 : Int) < radix) : 2 ≤ radix.toNat :=
  match intLessEqualDest isRadixAboveOne with
  | ⟨magnitudeBeyondTwo, radixEquation⟩ =>
      Nat.le.intro (congrArg Int.toNat radixEquation).symm

/-- A positive `Int` has a positive magnitude clamp — the same witness destruct one
rung down; this is what makes a positive power a POSITIVE `Nat` divisor for the
counting divider. -/
theorem intToNatPosOfPos {value : Int} (isPositive : (0 : Int) < value) :
    0 < value.toNat :=
  match intLessEqualDest isPositive with
  | ⟨magnitudeWitness, valueEquation⟩ =>
      Nat.le.intro (congrArg Int.toNat valueEquation).symm

/-- Magnitude division by `1` is the identity — ride `natDivModCountingByOne` through
both constructor arms (the `negSucc` arm's `-(Int.ofNat (n + 1))` collapse is
definitional). -/
theorem intMagnitudeQuotientByOne : ∀ mantissa : Int,
    intMagnitudeQuotient 1 mantissa = mantissa
  | .ofNat magnitude =>
      have quotientTransported :
          Int.ofNat (natDivModCounting magnitude 1).fst =
            Int.ofNat (magnitude, 0).fst :=
        congrArg (fun divModPair => Int.ofNat divModPair.fst)
          (natDivModCountingByOne magnitude)
      quotientTransported
  | .negSucc magnitudePredecessor =>
      have quotientTransported :
          -(Int.ofNat (natDivModCounting (magnitudePredecessor + 1) 1).fst) =
            -(Int.ofNat (magnitudePredecessor + 1, 0).fst) :=
        congrArg (fun divModPair => -(Int.ofNat divModPair.fst))
          (natDivModCountingByOne (magnitudePredecessor + 1))
      quotientTransported

/-! ## The order supplement — magnitude-quotient monotonicity + scaling invariance

The `Int` layer of rounding monotonicity (FLOAT-3c): the magnitude quotient is
sign-aware MONOTONE at a fixed divisor, and INVARIANT under scaling dividend and
divisor by one common positive factor.  Both ride the counting-divider certificates
(`natDivModCountingQuotientIsMonotone` / `natDivModCountingQuotientScales`); the sign
plumbing is `intNegLeNegOfLe` plus three small `ofNat`/`negSucc` order facts. -/

/-- Extract the `Nat` bound out of an `ofNat` bound — the inverse of
`intOfNatLeOfNat`: the additive witness re-reads through `Int.ofNat.inj` (the `Int`
sum of two `ofNat`s is definitionally the `ofNat` of the `Nat` sum). -/
theorem natLeOfIntOfNatLe {lowNat highNat : Nat}
    (isLessEqual : Int.ofNat lowNat ≤ Int.ofNat highNat) : lowNat ≤ highNat :=
  match intLessEqualDest isLessEqual with
  | ⟨_, differenceEquation⟩ =>
      Nat.le.intro (Int.ofNat.inj differenceEquation.symm)

/-- No `ofNat` sits below a `negSucc` — the destructed witness would equate the two
constructors. -/
theorem intFalseOfOfNatLeNegSucc {magnitude negSuccPredecessor : Nat}
    (isImpossible : Int.ofNat magnitude ≤ Int.negSucc negSuccPredecessor) : False :=
  match intLessEqualDest isImpossible with
  | ⟨_, differenceEquation⟩ => Int.noConfusion differenceEquation

/-- Every negated `ofNat` sits below every `ofNat` — the witness is the sum of the
two magnitudes, cancelled through `intAddLeftNeg`. -/
theorem intNegOfNatLeOfNat (leftMagnitude rightMagnitude : Nat) :
    -(Int.ofNat leftMagnitude) ≤ Int.ofNat rightMagnitude :=
  intLessEqualOfEqRight
    (intLessEqualIntro (-(Int.ofNat leftMagnitude))
      (leftMagnitude + rightMagnitude))
    ((intAddAssoc (-(Int.ofNat leftMagnitude)) (Int.ofNat leftMagnitude)
        (Int.ofNat rightMagnitude)).symm.trans
      ((congrArg (· + Int.ofNat rightMagnitude)
          (intAddLeftNeg (Int.ofNat leftMagnitude))).trans
        (intZeroAdd (Int.ofNat rightMagnitude))))

/-- **The magnitude quotient is monotone** — unconditional in the divisor, sign-aware
by the four-way constructor split: both-`ofNat` rides the counting divider's
monotonicity; an `ofNat` below a `negSucc` is impossible; a `negSucc` quotient sits
below every `ofNat` quotient outright; both-`negSucc` flips through
`intNegLeNegOfLe`, runs the divider on the REVERSED magnitudes, and flips back. -/
theorem intMagnitudeQuotientIsMonotone (divisor : Nat) :
    ∀ {lowValue highValue : Int}, lowValue ≤ highValue →
      intMagnitudeQuotient divisor lowValue ≤ intMagnitudeQuotient divisor highValue
  | .ofNat _, .ofNat _, isLessEqual =>
      intOfNatLeOfNat
        (natDivModCountingQuotientIsMonotone divisor
          (natLeOfIntOfNatLe isLessEqual))
  | .ofNat _, .negSucc _, isImpossible =>
      (intFalseOfOfNatLeNegSucc isImpossible).elim
  | .negSucc lowMagnitudePredecessor, .ofNat highMagnitude, _ =>
      intNegOfNatLeOfNat
        (natDivModCounting (lowMagnitudePredecessor + 1) divisor).fst
        (natDivModCounting highMagnitude divisor).fst
  | .negSucc _, .negSucc _, isLessEqual =>
      intNegLeNegOfLe
        (intOfNatLeOfNat
          (natDivModCountingQuotientIsMonotone divisor
            (natLeOfIntOfNatLe (intNegLeNegOfLe isLessEqual))))

/-- **Magnitude-quotient scaling invariance** — dividing a mantissa scaled by a
common positive factor by the equally-scaled divisor gives the original quotient.
The `ofNat` arm is the `Nat` scaling invariance under `congrArg`; the `negSucc` arm
destructs the scale to a successor so the scaled product reduces to a `negSucc`
(`negOfNat` needs a syntactic successor), then runs the same invariance on the
magnitude. -/
theorem intMagnitudeQuotientScales {divisor scaleFactor : Nat}
    (isDivisorPositive : 0 < divisor) (isScalePositive : 0 < scaleFactor) :
    ∀ mantissa : Int,
      intMagnitudeQuotient (divisor * scaleFactor)
          (mantissa * Int.ofNat scaleFactor) =
        intMagnitudeQuotient divisor mantissa
  | .ofNat magnitude =>
      congrArg Int.ofNat
        (natDivModCountingQuotientScales magnitude (divisor := divisor)
          (scaleFactor := scaleFactor) isDivisorPositive isScalePositive)
  | .negSucc magnitudePredecessor =>
      match scaleFactor, isScalePositive with
      | 0, impossibleBound => nomatch impossibleBound
      | scalePredecessor + 1, isSuccScalePositive =>
          congrArg (fun quotientMagnitude => -(Int.ofNat quotientMagnitude))
            (natDivModCountingQuotientScales (magnitudePredecessor + 1)
              (divisor := divisor) (scaleFactor := scalePredecessor + 1)
              isDivisorPositive isSuccScalePositive)

/-! ## The floor quotient — division toward negative infinity (FLOAT-3d)

The directed rounding modes correct the toward-zero quotient by one unit when the
dropped remainder is nonzero and points against the rounding direction.  Floor keeps
the magnitude quotient on `ofNat` mantissas and steps one below it on `negSucc`
mantissas with a nonzero remainder.  Two BRACKET certificates pin the semantics:
`floor * divisor` never exceeds the mantissa, and the mantissa sits strictly below
`floor * divisor + divisor` — together they make the floor quotient THE greatest
integer whose divisor-multiple is at or below the mantissa (the Galois-connection
form the carrier-level floor mode rides). -/

/-- The floor quotient: the magnitude quotient corrected one step down on a negative
mantissa with a nonzero remainder.  Written with `cond` so the Bool scrutinee stays
exposed for `congrArg` transport in the bracket proofs. -/
def intFloorQuotient (divisor : Nat) : Int → Int
  | .ofNat magnitude => Int.ofNat (natDivModCounting magnitude divisor).fst
  | .negSucc magnitudePredecessor =>
      cond ((natDivModCounting (magnitudePredecessor + 1) divisor).snd.beq 0)
        (-(Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).fst))
        (-(Int.ofNat
            ((natDivModCounting (magnitudePredecessor + 1) divisor).fst + 1)))

/-- **Lower bracket**: the floor quotient's divisor-multiple never exceeds the
mantissa.  The `ofNat` arm is the reconstruction witness; the exact `negSucc` arm is
an equality; the corrected `negSucc` arm negates `magnitude ≤ (quotient + 1) *
divisor`, which the remainder bound supplies. -/
theorem intFloorQuotientMulIsBelow {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ mantissa : Int,
      intFloorQuotient divisor mantissa * Int.ofNat divisor ≤ mantissa
  | .ofNat magnitude =>
      intOfNatLeOfNat
        (Nat.le.intro
          ((congrArg (· + (natDivModCounting magnitude divisor).snd)
              (Nat.mul_comm (natDivModCounting magnitude divisor).fst
                divisor)).trans
            (natDivModCountingReconstructs magnitude divisor).symm))
  | .negSucc magnitudePredecessor =>
      match beqEquation :
          (natDivModCounting (magnitudePredecessor + 1) divisor).snd.beq 0 with
      | true =>
          let quotientMagnitude :=
            (natDivModCounting (magnitudePredecessor + 1) divisor).fst
          let floorEquation :
              intFloorQuotient divisor (Int.negSucc magnitudePredecessor) =
                -(Int.ofNat quotientMagnitude) :=
            congrArg
              (fun conditionBool => cond conditionBool
                (-(Int.ofNat quotientMagnitude))
                (-(Int.ofNat (quotientMagnitude + 1))))
              beqEquation
          let magnitudeFactors :
              magnitudePredecessor + 1 = divisor * quotientMagnitude :=
            (natDivModCountingReconstructs (magnitudePredecessor + 1)
                divisor).trans
              (congrArg (divisor * quotientMagnitude + ·)
                (Nat.eq_of_beq_eq_true beqEquation))
          intLessEqualOfEqLeft
            ((congrArg (· * Int.ofNat divisor) floorEquation).trans
              ((intNegMul (Int.ofNat quotientMagnitude) (Int.ofNat divisor)).trans
                (congrArg (fun productNat => -(Int.ofNat productNat))
                  ((Nat.mul_comm quotientMagnitude divisor).trans
                    magnitudeFactors.symm))))
            (intLessEqualRefl (Int.negSucc magnitudePredecessor))
      | false =>
          let quotientMagnitude :=
            (natDivModCounting (magnitudePredecessor + 1) divisor).fst
          let floorEquation :
              intFloorQuotient divisor (Int.negSucc magnitudePredecessor) =
                -(Int.ofNat (quotientMagnitude + 1)) :=
            congrArg
              (fun conditionBool => cond conditionBool
                (-(Int.ofNat quotientMagnitude))
                (-(Int.ofNat (quotientMagnitude + 1))))
              beqEquation
          let magnitudeIsBelowSteppedMultiple :
              magnitudePredecessor + 1 ≤ (quotientMagnitude + 1) * divisor :=
            match Nat.le.dest
                (natDivModCountingRemainderIsBounded (magnitudePredecessor + 1)
                  divisor isDivisorPositive) with
            | ⟨boundWitness, boundEquation⟩ =>
                Nat.le.intro
                  ((congrArg (· + (1 + boundWitness))
                      (natDivModCountingReconstructs (magnitudePredecessor + 1)
                        divisor)).trans
                    ((Nat.add_assoc (divisor * quotientMagnitude)
                        (natDivModCounting (magnitudePredecessor + 1)
                          divisor).snd
                        (1 + boundWitness)).trans
                      ((congrArg (divisor * quotientMagnitude + ·)
                          (Nat.add_assoc
                            (natDivModCounting (magnitudePredecessor + 1)
                              divisor).snd
                            1 boundWitness).symm).trans
                        ((congrArg (divisor * quotientMagnitude + ·)
                            boundEquation).trans
                          ((congrArg (· + divisor)
                              (Nat.mul_comm divisor quotientMagnitude)).trans
                            (Nat.succ_mul quotientMagnitude divisor).symm)))))
          intLessEqualOfEqLeft
            ((congrArg (· * Int.ofNat divisor) floorEquation).trans
              (intNegMul (Int.ofNat (quotientMagnitude + 1)) (Int.ofNat divisor)))
            (intNegLeNegOfLe (intOfNatLeOfNat magnitudeIsBelowSteppedMultiple))

/-- **Upper bracket**: the mantissa sits strictly below the floor quotient's NEXT
divisor-multiple.  The `ofNat` arm rides the remainder bound; the exact `negSucc`
arm adds the divisor's positivity to the collapse equality; the corrected arm shifts
the mantissa by its positive remainder and telescopes the stepped multiple back. -/
theorem intFloorQuotientNextMultipleIsAbove {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ mantissa : Int,
      mantissa <
        intFloorQuotient divisor mantissa * Int.ofNat divisor + Int.ofNat divisor
  | .ofNat magnitude =>
      intOfNatLeOfNat
        (match Nat.le.dest
            (natDivModCountingRemainderIsBounded magnitude divisor
              isDivisorPositive) with
        | ⟨boundWitness, boundEquation⟩ =>
            Nat.le.intro
              ((congrArg (fun valueNat => (valueNat + 1) + boundWitness)
                  (natDivModCountingReconstructs magnitude divisor)).trans
                ((Nat.add_assoc
                    (divisor * (natDivModCounting magnitude divisor).fst)
                    ((natDivModCounting magnitude divisor).snd + 1)
                    boundWitness).trans
                  ((congrArg
                      (divisor * (natDivModCounting magnitude divisor).fst + ·)
                      boundEquation).trans
                    (congrArg (· + divisor)
                      (Nat.mul_comm divisor
                        (natDivModCounting magnitude divisor).fst))))))
  | .negSucc magnitudePredecessor =>
      match beqEquation :
          (natDivModCounting (magnitudePredecessor + 1) divisor).snd.beq 0 with
      | true =>
          let quotientMagnitude :=
            (natDivModCounting (magnitudePredecessor + 1) divisor).fst
          let floorEquation :
              intFloorQuotient divisor (Int.negSucc magnitudePredecessor) =
                -(Int.ofNat quotientMagnitude) :=
            congrArg
              (fun conditionBool => cond conditionBool
                (-(Int.ofNat quotientMagnitude))
                (-(Int.ofNat (quotientMagnitude + 1))))
              beqEquation
          let magnitudeFactors :
              magnitudePredecessor + 1 = divisor * quotientMagnitude :=
            (natDivModCountingReconstructs (magnitudePredecessor + 1)
                divisor).trans
              (congrArg (divisor * quotientMagnitude + ·)
                (Nat.eq_of_beq_eq_true beqEquation))
          let floorMulCollapses :
              intFloorQuotient divisor (Int.negSucc magnitudePredecessor) *
                  Int.ofNat divisor =
                -(Int.ofNat (magnitudePredecessor + 1)) :=
            (congrArg (· * Int.ofNat divisor) floorEquation).trans
              ((intNegMul (Int.ofNat quotientMagnitude) (Int.ofNat divisor)).trans
                (congrArg (fun productNat => -(Int.ofNat productNat))
                  ((Nat.mul_comm quotientMagnitude divisor).trans
                    magnitudeFactors.symm)))
          intLessEqualOfEqRight
            (intAddLeAddLeft (intOfNatLeOfNat isDivisorPositive)
              (-(Int.ofNat (magnitudePredecessor + 1))))
            (congrArg (· + Int.ofNat divisor) floorMulCollapses).symm
      | false =>
          let quotientMagnitude :=
            (natDivModCounting (magnitudePredecessor + 1) divisor).fst
          let remainderValue :=
            (natDivModCounting (magnitudePredecessor + 1) divisor).snd
          let floorEquation :
              intFloorQuotient divisor (Int.negSucc magnitudePredecessor) =
                -(Int.ofNat (quotientMagnitude + 1)) :=
            congrArg
              (fun conditionBool => cond conditionBool
                (-(Int.ofNat quotientMagnitude))
                (-(Int.ofNat (quotientMagnitude + 1))))
              beqEquation
          let remainderIsPositive : 0 < remainderValue :=
            natLtOfLeOfNe (natZeroLe remainderValue)
              (Ne.symm (Nat.ne_of_beq_eq_false beqEquation))
          let mantissaShiftCollapses :
              -(Int.ofNat (magnitudePredecessor + 1)) +
                  Int.ofNat remainderValue =
                -(Int.ofNat (divisor * quotientMagnitude)) :=
            (congrArg
                (fun magnitudeNat =>
                  -(Int.ofNat magnitudeNat) + Int.ofNat remainderValue)
                (natDivModCountingReconstructs (magnitudePredecessor + 1)
                  divisor)).trans
              ((congrArg (· + Int.ofNat remainderValue)
                  (intNegAdd (Int.ofNat (divisor * quotientMagnitude))
                    (Int.ofNat remainderValue))).trans
                ((intAddAssoc (-(Int.ofNat (divisor * quotientMagnitude)))
                    (-(Int.ofNat remainderValue))
                    (Int.ofNat remainderValue)).trans
                  ((congrArg
                      (-(Int.ofNat (divisor * quotientMagnitude)) + ·)
                      (intAddLeftNeg (Int.ofNat remainderValue))).trans
                    (intAddZero
                      (-(Int.ofNat (divisor * quotientMagnitude)))))))
          let steppedFloorMulCollapses :
              intFloorQuotient divisor (Int.negSucc magnitudePredecessor) *
                    Int.ofNat divisor + Int.ofNat divisor =
                -(Int.ofNat (divisor * quotientMagnitude)) :=
            (congrArg
                (fun floorValue =>
                  floorValue * Int.ofNat divisor + Int.ofNat divisor)
                floorEquation).trans
              ((congrArg (· + Int.ofNat divisor)
                  (intNegMul (Int.ofNat (quotientMagnitude + 1))
                    (Int.ofNat divisor))).trans
                ((congrArg
                    (fun productNat =>
                      -(Int.ofNat productNat) + Int.ofNat divisor)
                    (Nat.succ_mul quotientMagnitude divisor)).trans
                  ((congrArg (· + Int.ofNat divisor)
                      (intNegAdd (Int.ofNat (quotientMagnitude * divisor))
                        (Int.ofNat divisor))).trans
                    ((intAddAssoc
                        (-(Int.ofNat (quotientMagnitude * divisor)))
                        (-(Int.ofNat divisor)) (Int.ofNat divisor)).trans
                      ((congrArg
                          (-(Int.ofNat (quotientMagnitude * divisor)) + ·)
                          (intAddLeftNeg (Int.ofNat divisor))).trans
                        ((intAddZero
                            (-(Int.ofNat
                              (quotientMagnitude * divisor)))).trans
                          (congrArg
                            (fun productNat => -(Int.ofNat productNat))
                            (Nat.mul_comm quotientMagnitude divisor))))))))
          intLessEqualOfEqRight
            (intLessEqualOfEqRight
              (intAddLeAddLeft (intOfNatLeOfNat remainderIsPositive)
                (-(Int.ofNat (magnitudePredecessor + 1))))
              mantissaShiftCollapses)
            steppedFloorMulCollapses.symm

/-! ## The ceiling quotient — division toward positive infinity

Ceiling is floor REFLECTED: negate the mantissa, take the floor quotient, negate
back.  Both bracket certificates transport from the floor brackets through the
negation antitonicity — no fresh constructor analysis. -/

/-- The ceiling quotient: `-(floor (-mantissa))`. -/
def intCeilQuotient (divisor : Nat) (mantissa : Int) : Int :=
  -(intFloorQuotient divisor (-mantissa))

/-- **Lower bracket (dual)**: the ceiling quotient's divisor-multiple is at or above
the mantissa — negate the floor's lower bracket at the negated mantissa and pull the
sign into the product. -/
theorem intCeilQuotientMulIsAbove {divisor : Nat}
    (isDivisorPositive : 0 < divisor) (mantissa : Int) :
    mantissa ≤ intCeilQuotient divisor mantissa * Int.ofNat divisor :=
  intLessEqualOfEqLeft (intNegNeg mantissa).symm
    (intLessEqualOfEqRight
      (intNegLeNegOfLe (intFloorQuotientMulIsBelow isDivisorPositive (-mantissa)))
      (intNegMul (intFloorQuotient divisor (-mantissa)) (Int.ofNat divisor)).symm)

/-- **Strict upper bracket (dual)**: the ceiling quotient's PREVIOUS divisor-multiple
sits strictly below the mantissa, stated additively as `ceil * divisor < mantissa +
divisor` — negate the floor's strict bracket at the negated mantissa, split the
negated sum, and re-add the divisor across both sides. -/
theorem intCeilQuotientPreviousMultipleIsBelow {divisor : Nat}
    (isDivisorPositive : 0 < divisor) (mantissa : Int) :
    intCeilQuotient divisor mantissa * Int.ofNat divisor <
      mantissa + Int.ofNat divisor :=
  let ceilingMultiple := intCeilQuotient divisor mantissa * Int.ofNat divisor
  let negatedStrictBracket :
      -(intFloorQuotient divisor (-mantissa) * Int.ofNat divisor +
          Int.ofNat divisor) <
        mantissa :=
    intLessEqualOfEqRight
      (intNegLtNegOfLt
        (intFloorQuotientNextMultipleIsAbove isDivisorPositive (-mantissa)))
      (intNegNeg mantissa)
  let negatedSumSplits :
      -(intFloorQuotient divisor (-mantissa) * Int.ofNat divisor +
          Int.ofNat divisor) =
        ceilingMultiple + -(Int.ofNat divisor) :=
    (intNegAdd (intFloorQuotient divisor (-mantissa) * Int.ofNat divisor)
        (Int.ofNat divisor)).trans
      (congrArg (· + -(Int.ofNat divisor))
        (intNegMul (intFloorQuotient divisor (-mantissa))
          (Int.ofNat divisor)).symm)
  let shiftedBracket :
      (ceilingMultiple + -(Int.ofNat divisor)) + 1 ≤ mantissa :=
    intLessEqualOfEqLeft (congrArg (· + 1) negatedSumSplits).symm
      negatedStrictBracket
  intLessEqualOfEqLeft
    ((intAddAssoc (ceilingMultiple + -(Int.ofNat divisor)) 1
        (Int.ofNat divisor)).trans
      ((intAddAssoc ceilingMultiple (-(Int.ofNat divisor))
          (1 + Int.ofNat divisor)).trans
        (congrArg (ceilingMultiple + ·)
          ((congrArg (-(Int.ofNat divisor) + ·)
              (intAddComm 1 (Int.ofNat divisor))).trans
            ((intAddAssoc (-(Int.ofNat divisor)) (Int.ofNat divisor) 1).symm.trans
              ((congrArg (· + 1) (intAddLeftNeg (Int.ofNat divisor))).trans
                (intZeroAdd 1))))))).symm
    (intAddLeAddRight shiftedBracket (Int.ofNat divisor))

/-! ## The floor Galois adjunction

`intFloorQuotient` is the RIGHT ADJOINT to multiplication by the divisor:
`candidate * divisor ≤ mantissa ⟺ candidate ≤ floorQuotient divisor mantissa`.
The easy direction rides the lower bracket; the hard direction is discreteness —
a candidate strictly above the floor pushes its multiple past the strict upper
bracket, collapsing to `mantissa + 1 ≤ mantissa`. -/

/-- No integer sits at or above its own successor — the `Int` twin of
`natSuccNeverLeSelf`: destruct the witness, left-cancel, and read the impossible
`0 = successor` off the `ofNat` constructor. -/
theorem intSuccNeverLeSelf {value : Int} (isSuccLeSelf : value + 1 ≤ value) : False :=
  match intLessEqualDest isSuccLeSelf with
  | ⟨difference, differenceEquation⟩ =>
      have collapseAfterCancel : ∀ tailSummand : Int,
          -value + (value + tailSummand) = tailSummand := fun tailSummand =>
        (intAddAssoc (-value) value tailSummand).symm.trans
          ((congrArg (· + tailSummand) (intAddLeftNeg value)).trans
            (intZeroAdd tailSummand))
      have paddedSumsAgree : value + 0 = value + (1 + Int.ofNat difference) :=
        (intAddZero value).trans
          (differenceEquation.trans (intAddAssoc value 1 (Int.ofNat difference)))
      have zeroEqualsSuccessor : (0 : Int) = Int.ofNat (difference + 1) :=
        ((collapseAfterCancel 0).symm.trans
          ((congrArg (-value + ·) paddedSumsAgree).trans
            (collapseAfterCancel (1 + Int.ofNat difference)))).trans
          (intAddComm 1 (Int.ofNat difference))
      Nat.noConfusion (Int.ofNat.inj zeroEqualsSuccessor)

/-- **Galois, easy direction**: below the floor quotient means the multiple is below
the mantissa — scale the bound by the divisor and chain through the lower bracket. -/
theorem intMulLeMantissaOfLeFloorQuotient {divisor : Nat}
    (isDivisorPositive : 0 < divisor) {candidate mantissa : Int}
    (isBelowQuotient : candidate ≤ intFloorQuotient divisor mantissa) :
    candidate * Int.ofNat divisor ≤ mantissa :=
  intLessEqualTrans
    (intMulLeMulRightOfNonNeg isBelowQuotient (intZeroLeOfNat divisor))
    (intFloorQuotientMulIsBelow isDivisorPositive mantissa)

/-- **Galois, hard direction (discreteness)**: a multiple below the mantissa forces
the candidate at or below the floor quotient.  Total order splits candidate vs
quotient; a candidate strictly above (successor gap) scales past the strict upper
bracket and collapses to `mantissa + 1 ≤ mantissa`. -/
theorem intLeFloorQuotientOfMulLe {divisor : Nat} (isDivisorPositive : 0 < divisor)
    {candidate mantissa : Int}
    (isMultipleBelow : candidate * Int.ofNat divisor ≤ mantissa) :
    candidate ≤ intFloorQuotient divisor mantissa :=
  match intLessEqualTotal candidate (intFloorQuotient divisor mantissa) with
  | .inl isCandidateBelow => isCandidateBelow
  | .inr isFloorBelow =>
      match intLessEqualDest isFloorBelow with
      | ⟨0, gapEquation⟩ =>
          intLessEqualOfEqLeft
            (gapEquation.trans (intAddZero (intFloorQuotient divisor mantissa)))
            (intLessEqualRefl (intFloorQuotient divisor mantissa))
      | ⟨gapPredecessor + 1, gapEquation⟩ =>
          have floorSuccessorLeCandidate :
              intFloorQuotient divisor mantissa + 1 ≤ candidate :=
            intLessEqualOfEqRight
              (intLessEqualIntro
                (intFloorQuotient divisor mantissa + 1) gapPredecessor)
              ((intAddAssoc (intFloorQuotient divisor mantissa) 1
                  (Int.ofNat gapPredecessor)).trans
                ((congrArg (intFloorQuotient divisor mantissa + ·)
                  (intAddComm 1 (Int.ofNat gapPredecessor))).trans
                  gapEquation.symm))
          have strictBracketFolds :
              intFloorQuotient divisor mantissa * Int.ofNat divisor +
                  Int.ofNat divisor =
                (intFloorQuotient divisor mantissa + 1) * Int.ofNat divisor :=
            ((intRightDistrib (intFloorQuotient divisor mantissa) 1
                (Int.ofNat divisor)).trans
              (congrArg
                (intFloorQuotient divisor mantissa * Int.ofNat divisor + ·)
                (intOneMul (Int.ofNat divisor)))).symm
          (intSuccNeverLeSelf
            (intLessEqualTrans
              (intLessEqualTrans
                (intLessEqualOfEqRight
                  (intFloorQuotientNextMultipleIsAbove isDivisorPositive mantissa)
                  strictBracketFolds)
                (intMulLeMulRightOfNonNeg floorSuccessorLeCandidate
                  (intZeroLeOfNat divisor)))
              isMultipleBelow)).elim

/-! ## The ceiling Galois adjunction — by reflection

`intCeilQuotient` is the LEFT adjoint to multiplication by the divisor:
`ceilQuotient divisor mantissa ≤ candidate ⟺ mantissa ≤ candidate * divisor`.
Both directions transport across `ceil = −floor(−·)`: negate, apply the floor
adjunction, negate back. -/

/-- **Galois, easy direction**: above the ceiling quotient means the multiple is
above the mantissa — the upper bracket chained with the scaled bound. -/
theorem intMantissaLeMulOfCeilQuotientLe {divisor : Nat}
    (isDivisorPositive : 0 < divisor) {candidate mantissa : Int}
    (isAboveQuotient : intCeilQuotient divisor mantissa ≤ candidate) :
    mantissa ≤ candidate * Int.ofNat divisor :=
  intLessEqualTrans (intCeilQuotientMulIsAbove isDivisorPositive mantissa)
    (intMulLeMulRightOfNonNeg isAboveQuotient (intZeroLeOfNat divisor))

/-- **Galois, hard direction (discreteness), by reflection**: a multiple above the
mantissa forces the candidate at or above the ceiling quotient.  Negate the bound,
push the negation into the product, apply the floor adjunction at `−mantissa`, and
negate back — the double negation on the candidate cancels. -/
theorem intCeilQuotientLeOfMantissaLeMul {divisor : Nat}
    (isDivisorPositive : 0 < divisor) {candidate mantissa : Int}
    (isMultipleAbove : mantissa ≤ candidate * Int.ofNat divisor) :
    intCeilQuotient divisor mantissa ≤ candidate :=
  intLessEqualOfEqRight
    (intNegLeNegOfLe
      (intLeFloorQuotientOfMulLe isDivisorPositive
        (intLessEqualOfEqLeft
          (intNegMul candidate (Int.ofNat divisor))
          (intNegLeNegOfLe isMultipleAbove))))
    (intNegNeg candidate)

/-! ## The away-from-zero quotient

Round away from zero = grow the magnitude: ceiling behavior on nonnegative
mantissas, floor behavior on negative ones — one constructor dispatch, so every
bracket is inherited from the shipped ceiling/floor certificates.  Not an IEEE
rounding-direction attribute by itself; it is the quotient core of the
`roundTiesToAway` tie-break. -/

/-- **Round away from zero** — the sign-directed quotient correction. -/
def intAwayQuotient (divisor : Nat) : Int → Int
  | .ofNat magnitude => intCeilQuotient divisor (Int.ofNat magnitude)
  | .negSucc magnitudePredecessor =>
      intFloorQuotient divisor (Int.negSucc magnitudePredecessor)

/-- On nonnegative mantissas the away multiple sits at or above — the ceiling
bracket read through the dispatch. -/
theorem intAwayQuotientMulIsAboveOfNonNegativeMantissa {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ {mantissa : Int}, (0 : Int) ≤ mantissa →
      mantissa ≤ intAwayQuotient divisor mantissa * Int.ofNat divisor
  | .ofNat magnitude, _ =>
      intCeilQuotientMulIsAbove isDivisorPositive (Int.ofNat magnitude)
  | .negSucc _, isImpossible => (intFalseOfOfNatLeNegSucc isImpossible).elim

/-- On nonnegative mantissas the away multiple overshoots by less than one
divisor — the strict ceiling bracket read through the dispatch. -/
theorem intAwayQuotientPreviousMultipleIsBelowOfNonNegativeMantissa {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ {mantissa : Int}, (0 : Int) ≤ mantissa →
      intAwayQuotient divisor mantissa * Int.ofNat divisor <
        mantissa + Int.ofNat divisor
  | .ofNat magnitude, _ =>
      intCeilQuotientPreviousMultipleIsBelow isDivisorPositive (Int.ofNat magnitude)
  | .negSucc _, isImpossible => (intFalseOfOfNatLeNegSucc isImpossible).elim

/-- On negative mantissas the away multiple sits at or below — the floor bracket
read through the dispatch. -/
theorem intAwayQuotientMulIsBelowOfNegativeMantissa {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ {mantissa : Int}, mantissa < 0 →
      intAwayQuotient divisor mantissa * Int.ofNat divisor ≤ mantissa
  | .ofNat _, isImpossible => nomatch natLeOfIntOfNatLe isImpossible
  | .negSucc magnitudePredecessor, _ =>
      intFloorQuotientMulIsBelow isDivisorPositive
        (Int.negSucc magnitudePredecessor)

/-- On negative mantissas the away multiple undershoots by less than one divisor
— the strict floor bracket read through the dispatch. -/
theorem intAwayQuotientNextMultipleIsAboveOfNegativeMantissa {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ {mantissa : Int}, mantissa < 0 →
      mantissa <
        intAwayQuotient divisor mantissa * Int.ofNat divisor + Int.ofNat divisor
  | .ofNat _, isImpossible => nomatch natLeOfIntOfNatLe isImpossible
  | .negSucc magnitudePredecessor, _ =>
      intFloorQuotientNextMultipleIsAbove isDivisorPositive
        (Int.negSucc magnitudePredecessor)

/-! ## Round-nearest-ties-even on Int mantissas — by sign reflection

Ties-to-even is sign-symmetric (a quotient and its negation share parity), so the
negative arm is the NEGATED magnitude correction.  Each doubled half-ulp bracket
transports from the Nat pair: the `ofNat` arm is the lifted Nat bound verbatim (all
the `ofNat` arithmetic is definitional), and the `negSucc` arm negates the OPPOSITE
Nat bound and shifts it back by one divisor. -/

/-- Push a negated factor out of the doubled product. -/
theorem intMulTwiceNegFolds (leftFactor rightFactor : Int) :
    2 * (leftFactor * -rightFactor) = -(2 * (leftFactor * rightFactor)) :=
  (congrArg (2 * ·) (intMulNeg leftFactor rightFactor)).trans
    (intMulNeg 2 (leftFactor * rightFactor))

/-- Shifting a negated sum back by its own tail recovers the negated head. -/
theorem intNegAddShiftCollapses (centerValue shiftValue : Int) :
    -(centerValue + shiftValue) + shiftValue = -centerValue :=
  (congrArg (· + shiftValue) (intNegAdd centerValue shiftValue)).trans
    ((intAddAssoc (-centerValue) (-shiftValue) shiftValue).trans
      ((congrArg (-centerValue + ·) (intAddLeftNeg shiftValue)).trans
        (intAddZero (-centerValue))))

/-- **Round-nearest-ties-even quotient** — the Nat corrector reflected by sign. -/
def intNearestEvenQuotient (divisor : Nat) : Int → Int
  | .ofNat magnitude => Int.ofNat (natNearestEvenQuotient divisor magnitude)
  | .negSucc magnitudePredecessor =>
      -(Int.ofNat (natNearestEvenQuotient divisor (magnitudePredecessor + 1)))

/-- **Doubled half-ulp, below**: twice the nearest multiple never exceeds twice the
mantissa by more than one divisor. -/
theorem intNearestEvenQuotientMulTwiceIsBelow {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ mantissa : Int,
      2 * (Int.ofNat divisor * intNearestEvenQuotient divisor mantissa) ≤
        2 * mantissa + Int.ofNat divisor
  | .ofNat magnitude =>
      intOfNatLeOfNat (natNearestEvenQuotientMulTwiceIsBelow divisor magnitude)
  | .negSucc magnitudePredecessor =>
      intLessEqualOfEqLeft
        (intMulTwiceNegFolds (Int.ofNat divisor)
          (Int.ofNat (natNearestEvenQuotient divisor (magnitudePredecessor + 1))))
        (intLessEqualOfEqLeft
          (intNegAddShiftCollapses
            (2 * (Int.ofNat divisor *
              Int.ofNat
                (natNearestEvenQuotient divisor (magnitudePredecessor + 1))))
            (Int.ofNat divisor)).symm
          (intAddLeAddRight
            (intNegLeNegOfLe
              (intOfNatLeOfNat
                (natNearestEvenQuotientMulTwiceIsAbove isDivisorPositive
                  (magnitudePredecessor + 1))))
            (Int.ofNat divisor)))

/-- **Doubled half-ulp, above**: twice the mantissa never exceeds twice the nearest
multiple by more than one divisor. -/
theorem intNearestEvenQuotientMulTwiceIsAbove {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ mantissa : Int,
      2 * mantissa ≤
        2 * (Int.ofNat divisor * intNearestEvenQuotient divisor mantissa) +
          Int.ofNat divisor
  | .ofNat magnitude =>
      intOfNatLeOfNat
        (natNearestEvenQuotientMulTwiceIsAbove isDivisorPositive magnitude)
  | .negSucc magnitudePredecessor =>
      have doubledMagnitudeBound :
          -(2 * Int.ofNat (magnitudePredecessor + 1)) ≤
            2 * (Int.ofNat divisor *
                -Int.ofNat
                  (natNearestEvenQuotient divisor (magnitudePredecessor + 1))) +
              Int.ofNat divisor :=
        intLessEqualOfEqRight
          (intLessEqualOfEqLeft
            (intNegAddShiftCollapses (2 * Int.ofNat (magnitudePredecessor + 1))
              (Int.ofNat divisor)).symm
            (intAddLeAddRight
              (intNegLeNegOfLe
                (intOfNatLeOfNat
                  (natNearestEvenQuotientMulTwiceIsBelow divisor
                    (magnitudePredecessor + 1))))
              (Int.ofNat divisor)))
          (congrArg (· + Int.ofNat divisor)
            (intMulTwiceNegFolds (Int.ofNat divisor)
              (Int.ofNat
                (natNearestEvenQuotient divisor (magnitudePredecessor + 1)))).symm)
      doubledMagnitudeBound

/-! ## Faithfulness: the nearest quotient is the floor or the ceiling

Sign reflection swaps the sides: on a nonnegative mantissa keeping lands on the
floor and bumping on the ceiling; on a negative mantissa keeping lands on the
CEILING (there the magnitude quotient IS the ceiling, definitionally) and bumping
on the floor.  The bump's midpoint certificate forces the nonzero remainder that
pins the corrected floor branch. -/

/-- With a nonzero remainder the `negSucc` floor takes the corrected branch. -/
theorem intFloorQuotientAtNegSuccOfPositiveRemainder {divisor : Nat}
    (magnitudePredecessor : Nat)
    (isRemainderPositive :
      0 < (natDivModCounting (magnitudePredecessor + 1) divisor).snd) :
    intFloorQuotient divisor (Int.negSucc magnitudePredecessor) =
      -(Int.ofNat
        ((natDivModCounting (magnitudePredecessor + 1) divisor).fst + 1)) :=
  congrArg
    (fun exactFlag => cond exactFlag
      (-(Int.ofNat (natDivModCounting (magnitudePredecessor + 1) divisor).fst))
      (-(Int.ofNat
        ((natDivModCounting (magnitudePredecessor + 1) divisor).fst + 1))))
    (natBeqZeroEqFalseOfPos isRemainderPositive)

/-- With a nonzero remainder the ceiling at a nonnegative mantissa is the successor
of the counting quotient — reflect to the `negSucc` floor and cancel the double
negation.  A zero magnitude has a zero remainder, so that arm is impossible. -/
theorem intCeilQuotientAtOfNatOfPositiveRemainder {divisor : Nat} :
    ∀ magnitude : Nat,
      0 < (natDivModCounting magnitude divisor).snd →
      intCeilQuotient divisor (Int.ofNat magnitude) =
        Int.ofNat ((natDivModCounting magnitude divisor).fst + 1)
  | 0, isRemainderPositive => nomatch isRemainderPositive
  | magnitudePredecessor + 1, isRemainderPositive =>
      (congrArg Int.neg
        (intFloorQuotientAtNegSuccOfPositiveRemainder magnitudePredecessor
          isRemainderPositive)).trans
        (intNegNeg (Int.ofNat
          ((natDivModCounting (magnitudePredecessor + 1) divisor).fst + 1)))

/-- **Faithfulness**: the nearest quotient IS the floor or the ceiling — never
anything else.  Dispatch the kept-or-bumped disjunction per constructor arm; the
kept side is definitional (floor on `ofNat`, ceiling on `negSucc`), the bumped side
derives the nonzero remainder from the midpoint certificate and lands on the
corrected branch of the other rounding. -/
theorem intNearestEvenQuotientIsFloorOrCeil {divisor : Nat}
    (isDivisorPositive : 0 < divisor) :
    ∀ mantissa : Int,
      intNearestEvenQuotient divisor mantissa = intFloorQuotient divisor mantissa ∨
        intNearestEvenQuotient divisor mantissa = intCeilQuotient divisor mantissa
  | .ofNat magnitude =>
      match natNearestEvenQuotientIsKeptOrBumpedWithMidpointCertificate divisor
          magnitude with
      | .inl keptEquation => .inl (congrArg Int.ofNat keptEquation)
      | .inr ⟨bumpedEquation, midpointCertificate⟩ =>
          .inr ((congrArg Int.ofNat bumpedEquation).trans
            (intCeilQuotientAtOfNatOfPositiveRemainder magnitude
              (natPosOfDoublePos
                (natLeTrans isDivisorPositive midpointCertificate))).symm)
  | .negSucc magnitudePredecessor =>
      match natNearestEvenQuotientIsKeptOrBumpedWithMidpointCertificate divisor
          (magnitudePredecessor + 1) with
      | .inl keptEquation =>
          .inr (congrArg (fun quotientValue => -(Int.ofNat quotientValue))
            keptEquation)
      | .inr ⟨bumpedEquation, midpointCertificate⟩ =>
          .inl ((congrArg (fun quotientValue => -(Int.ofNat quotientValue))
            bumpedEquation).trans
            (intFloorQuotientAtNegSuccOfPositiveRemainder magnitudePredecessor
              (natPosOfDoublePos
                (natLeTrans isDivisorPositive midpointCertificate))).symm)

end FX1Poly.ComputerAlgebra
