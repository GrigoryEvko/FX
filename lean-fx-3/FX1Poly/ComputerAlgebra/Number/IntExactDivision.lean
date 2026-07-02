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

end FX1Poly.ComputerAlgebra
