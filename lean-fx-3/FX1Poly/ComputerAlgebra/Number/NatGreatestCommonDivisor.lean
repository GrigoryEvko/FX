import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity
import FX1Poly.ComputerAlgebra.Number.IntOrderCore
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision

/-! # Counting Euclid — the natural-number gcd

Init's `Nat.gcd` is defined by well-founded recursion, which is unavailable here:
`WellFounded.fix` does not compute by kernel reduction and its equation lemmas leak
`propext`. Euclid's algorithm is recursed structurally on a fuel argument over the
counting divider (`natDivModCounting`), with the divides certificates proved by the same
fuel induction.

  * `NatDivides divisor value` is explicit-witness divisibility
    `∃ quotient, value = divisor * quotient`, the divisor on the LEFT to match the
    counting divider's reconstruction shape, so a multiple-of-the-divisor step is one
    `natMulAssoc`.
  * `natGcdWithFuel` recurses on fuel only; the Euclid step swaps
    `(leftValue, rightValue) ↦ (rightValue mod leftValue, leftValue)`, and the remainder
    bound keeps the invariant `leftValue < fuel`, so `fuel = leftValue + 1` always
    suffices (`natGcd`).
  * The divides-left and divides-right certificates are entangled through the argument
    swap, so `natGcdWithFuelDividesBoth` proves the conjunction in ONE induction; the
    wrappers project it.

The extended-Euclid layer rides the same fuel induction. The Bezout identity
`NatBezoutIdentityFor` is the Nat-safe disjunctive form `s*a = t*b + g ∨ t*b = s*a + g`
(the ℤ coefficients' signs become the disjunct), maintained through Euclid's swap by the
coefficient update `(s', t') ↦ (s'*Q + t', s')`, which flips the disjunct. Greatest-ness
(`natDividesGcdOfDividesBoth`) follows without a second induction: scale the common
divisor into the identity and cancel a summand (`natDividesAddCancelLeft`, discharged by
Euclidean quotient uniqueness against the zero remainder). One caveat: fuel-irrelevance —
the recurrence equation between `natGcd` calls at different fuels — is not established
here.

Structural fuel recursion, `Exists` witness arithmetic over `congrArg`/`Eq.trans`, and
`nomatch` on the empty fuel-exhausted bound; free of `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`, and `WellFounded.fix`.
Per-declaration gated in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Divisibility with explicit witnesses -/

/-- `divisor` divides `value`, witnessed by the cofactor.  The divisor sits on
the LEFT of the product so the counting divider's reconstruction
`dividend = divisor * quotient + remainder` plugs in without commutations. -/
def NatDivides (divisor value : Nat) : Prop :=
  ∃ quotient, value = divisor * quotient

/-- Everything divides zero — `divisor * 0` reduces definitionally. -/
theorem natDividesZero (divisor : Nat) : NatDivides divisor 0 :=
  ⟨0, rfl⟩

/-- Everything divides itself — `value * 1` is `0 + value` definitionally. -/
theorem natDividesRefl (value : Nat) : NatDivides value value :=
  ⟨1, (Nat.zero_add value).symm⟩

/-- Transport divisibility along an equality of the divided value. -/
theorem natDividesOfEq {divisor value otherValue : Nat}
    (areEqual : otherValue = value) (divides : NatDivides divisor value) :
    NatDivides divisor otherValue :=
  match divides with
  | ⟨quotient, valueEquation⟩ => ⟨quotient, areEqual.trans valueEquation⟩

/-- A divisor of `value` divides every right multiple of `value` — one
associativity step on the witness. -/
theorem natDividesMulRight {divisor value : Nat} (scaleFactor : Nat)
    (divides : NatDivides divisor value) :
    NatDivides divisor (value * scaleFactor) :=
  match divides with
  | ⟨quotient, valueEquation⟩ =>
      ⟨quotient * scaleFactor,
        (congrArg (· * scaleFactor) valueEquation).trans
          (natMulAssoc divisor quotient scaleFactor)⟩

/-- A common divisor divides the sum — the witnesses add through left
distributivity. -/
theorem natDividesAdd {divisor leftValue rightValue : Nat}
    (dividesLeft : NatDivides divisor leftValue)
    (dividesRight : NatDivides divisor rightValue) :
    NatDivides divisor (leftValue + rightValue) :=
  match dividesLeft, dividesRight with
  | ⟨leftQuotient, leftEquation⟩, ⟨rightQuotient, rightEquation⟩ =>
      ⟨leftQuotient + rightQuotient,
        (congrArg (· + rightValue) leftEquation).trans
          ((congrArg (divisor * leftQuotient + ·) rightEquation).trans
            (Nat.left_distrib divisor leftQuotient rightQuotient).symm)⟩

/-- A divisor of a successor is positive — a zero divisor would make the
successor a zero product. -/
theorem natDivisorOfSuccIsPositive {divisor valuePredecessor : Nat}
    (divides : NatDivides divisor (valuePredecessor + 1)) : 0 < divisor :=
  match divisor, divides with
  | 0, ⟨quotient, valueEquation⟩ =>
      Nat.noConfusion (valueEquation.trans (Nat.zero_mul quotient))
  | divisorPredecessor + 1, _ =>
      natSuccLeSuccOfLe (natZeroLe divisorPredecessor)

/-! ## Euclid's algorithm, structural on fuel -/

/-- Euclid by counting division, STRUCTURAL on the fuel (never
`WellFounded.fix`).  The step swaps in the remainder:
`gcd(a, b) = gcd(b mod a, a)`.  The first argument strictly decreases, so any
`fuel > leftValue` reaches the zero base case; the fuel-exhausted arm returns
`rightValue` so that `gcd(0, b) = b` holds at EVERY fuel. -/
def natGcdWithFuel : Nat → Nat → Nat → Nat
  | 0, _, rightValue => rightValue
  | _ + 1, 0, rightValue => rightValue
  | fuel + 1, leftPredecessor + 1, rightValue =>
      natGcdWithFuel fuel
        (natDivModCounting rightValue (leftPredecessor + 1)).snd
        (leftPredecessor + 1)

/-- **The divides certificates, jointly** — the two sides are entangled through
Euclid's argument swap, so one fuel induction carries the conjunction: the
callee's divides-right IS the caller's divides-left, and the caller's
divides-right recombines the callee's pair through the reconstruction
`rightValue = leftValue * quotient + remainder`. -/
theorem natGcdWithFuelDividesBoth : ∀ fuel leftValue rightValue : Nat,
    leftValue < fuel →
    NatDivides (natGcdWithFuel fuel leftValue rightValue) leftValue ∧
    NatDivides (natGcdWithFuel fuel leftValue rightValue) rightValue
  | 0, _, _, isBelowFuel => nomatch isBelowFuel
  | _ + 1, 0, rightValue, _ =>
      ⟨natDividesZero rightValue, natDividesRefl rightValue⟩
  | fuel + 1, leftPredecessor + 1, rightValue, isBelowFuel =>
      have remainderIsBelowFuel :
          (natDivModCounting rightValue (leftPredecessor + 1)).snd < fuel :=
        natLeTrans
          (natDivModCountingRemainderIsBounded rightValue (leftPredecessor + 1)
            (natSuccLeSuccOfLe (natZeroLe leftPredecessor)))
          (Nat.le_of_succ_le_succ isBelowFuel)
      match natGcdWithFuelDividesBoth fuel
          (natDivModCounting rightValue (leftPredecessor + 1)).snd
          (leftPredecessor + 1) remainderIsBelowFuel with
      | ⟨dividesRemainder, dividesLeftSucc⟩ =>
          ⟨dividesLeftSucc,
            natDividesOfEq
              (natDivModCountingReconstructs rightValue (leftPredecessor + 1))
              (natDividesAdd
                (natDividesMulRight
                  (natDivModCounting rightValue (leftPredecessor + 1)).fst
                  dividesLeftSucc)
                dividesRemainder)⟩

/-! ## The canonical-fuel wrapper -/

/-- The greatest common divisor — `fuel = leftValue + 1` always suffices
because the first argument strictly decreases along Euclid's swap. -/
def natGcd (leftValue rightValue : Nat) : Nat :=
  natGcdWithFuel (leftValue + 1) leftValue rightValue

/-- `gcd(0, b) = b`, definitionally. -/
theorem natGcdZeroLeft (rightValue : Nat) : natGcd 0 rightValue = rightValue :=
  rfl

/-- The gcd divides its left argument. -/
theorem natGcdDividesLeft (leftValue rightValue : Nat) :
    NatDivides (natGcd leftValue rightValue) leftValue :=
  (natGcdWithFuelDividesBoth (leftValue + 1) leftValue rightValue
    Nat.le.refl).left

/-- The gcd divides its right argument. -/
theorem natGcdDividesRight (leftValue rightValue : Nat) :
    NatDivides (natGcd leftValue rightValue) rightValue :=
  (natGcdWithFuelDividesBoth (leftValue + 1) leftValue rightValue
    Nat.le.refl).right

/-- The gcd of a positive left argument is positive — it divides that
successor.  (The normalized-denominator positivity supplier for the ℚ
canonical form.) -/
theorem natGcdOfSuccLeftIsPositive (leftPredecessor rightValue : Nat) :
    0 < natGcd (leftPredecessor + 1) rightValue :=
  natDivisorOfSuccIsPositive (natGcdDividesLeft (leftPredecessor + 1) rightValue)

/-! ## Extended Euclid — the Bezout identity -/

/-- A divisor of `value` divides every left multiple of `value` — commute the
scale across the witness and re-associate. -/
theorem natDividesMulLeft {divisor value : Nat} (scaleFactor : Nat)
    (divides : NatDivides divisor value) :
    NatDivides divisor (scaleFactor * value) :=
  match divides with
  | ⟨quotient, valueEquation⟩ =>
      ⟨quotient * scaleFactor,
        (congrArg (scaleFactor * ·) valueEquation).trans
          ((Nat.mul_comm scaleFactor (divisor * quotient)).trans
            (natMulAssoc divisor quotient scaleFactor))⟩

/-- **Summand cancellation**: a divisor of one summand and of the sum divides
the other summand.  Nat has no subtraction to reach for, so the residual
quotient is read off the counting divider: the sum equation makes
`divisor * (leftQuotient + quotient) + remainder` and
`divisor * sumQuotient + 0` two Euclidean decompositions of the same number,
and quotient uniqueness forces the remainder to zero. -/
theorem natDividesAddCancelLeft {divisor leftValue rightValue : Nat}
    (dividesLeft : NatDivides divisor leftValue)
    (dividesSum : NatDivides divisor (leftValue + rightValue)) :
    NatDivides divisor rightValue :=
  match divisor, dividesLeft, dividesSum with
  | 0, ⟨leftQuotient, leftEquation⟩, ⟨sumQuotient, sumEquation⟩ =>
      have leftIsZero : leftValue = 0 :=
        leftEquation.trans (Nat.zero_mul leftQuotient)
      have sumIsZero : leftValue + rightValue = 0 :=
        sumEquation.trans (Nat.zero_mul sumQuotient)
      have rightIsZero : rightValue = 0 :=
        natAddEqZeroLeft
          ((Nat.add_comm rightValue leftValue).trans sumIsZero)
      ⟨0, rightIsZero⟩
  | divisorPredecessor + 1, ⟨leftQuotient, leftEquation⟩,
      ⟨sumQuotient, sumEquation⟩ =>
      have divisorIsPositive : 0 < divisorPredecessor + 1 :=
        natSuccLeSuccOfLe (natZeroLe divisorPredecessor)
      have combined :
          (divisorPredecessor + 1) * leftQuotient + rightValue =
            (divisorPredecessor + 1) * sumQuotient :=
        (congrArg (· + rightValue) leftEquation.symm).trans sumEquation
      have fullDecomposition :
          (divisorPredecessor + 1) *
              (leftQuotient +
                (natDivModCounting rightValue (divisorPredecessor + 1)).fst) +
              (natDivModCounting rightValue (divisorPredecessor + 1)).snd =
            (divisorPredecessor + 1) * sumQuotient + 0 :=
        (congrArg
            (· + (natDivModCounting rightValue (divisorPredecessor + 1)).snd)
            (Nat.left_distrib (divisorPredecessor + 1) leftQuotient
              (natDivModCounting rightValue (divisorPredecessor + 1)).fst)).trans
          ((Nat.add_assoc ((divisorPredecessor + 1) * leftQuotient)
              ((divisorPredecessor + 1) *
                (natDivModCounting rightValue (divisorPredecessor + 1)).fst)
              (natDivModCounting rightValue (divisorPredecessor + 1)).snd).trans
            ((congrArg ((divisorPredecessor + 1) * leftQuotient + ·)
                (natDivModCountingReconstructs rightValue
                  (divisorPredecessor + 1)).symm).trans
              combined))
      have quotientsAgree :
          leftQuotient +
              (natDivModCounting rightValue (divisorPredecessor + 1)).fst =
            sumQuotient :=
        natEuclideanQuotientUnique
          (natDivModCountingRemainderIsBounded rightValue
            (divisorPredecessor + 1) divisorIsPositive)
          divisorIsPositive fullDecomposition
      have remainderIsZero :
          (natDivModCounting rightValue (divisorPredecessor + 1)).snd = 0 :=
        natAddLeftCancel
          ((congrArg
              (fun combinedQuotient =>
                (divisorPredecessor + 1) * combinedQuotient +
                  (natDivModCounting rightValue (divisorPredecessor + 1)).snd)
              quotientsAgree).symm.trans
            fullDecomposition)
      ⟨(natDivModCounting rightValue (divisorPredecessor + 1)).fst,
        (natDivModCountingReconstructs rightValue
            (divisorPredecessor + 1)).trans
          (congrArg
            ((divisorPredecessor + 1) *
                (natDivModCounting rightValue (divisorPredecessor + 1)).fst + ·)
            remainderIsZero)⟩

/-- **The Nat-safe Bezout identity**: over ℤ the gcd is `s*a + t*b` with
coefficients of opposite signs; over Nat the sign becomes a DISJUNCT.  Which
disjunct holds flips at every Euclid step. -/
def NatBezoutIdentityFor (gcdValue leftValue rightValue : Nat) : Prop :=
  ∃ leftCoefficient rightCoefficient,
    leftCoefficient * leftValue = rightCoefficient * rightValue + gcdValue ∨
    rightCoefficient * rightValue = leftCoefficient * leftValue + gcdValue

/-- **Extended Euclid** — the Bezout identity rides the same fuel induction as
the divides certificates: the step substitutes the reconstruction
`rightValue = leftValue * quotient + remainder` into the callee's identity,
updating the coefficients by `(s', t') ↦ (s'*quotient + t', s')` and flipping
the disjunct. -/
theorem natGcdWithFuelBezout : ∀ fuel leftValue rightValue : Nat,
    leftValue < fuel →
    NatBezoutIdentityFor (natGcdWithFuel fuel leftValue rightValue) leftValue
      rightValue
  | 0, _, _, isBelowFuel => nomatch isBelowFuel
  | _ + 1, 0, rightValue, _ => ⟨0, 1, .inr (Nat.mul_comm 1 rightValue)⟩
  | fuel + 1, leftPredecessor + 1, rightValue, isBelowFuel =>
      have remainderIsBelowFuel :
          (natDivModCounting rightValue (leftPredecessor + 1)).snd < fuel :=
        natLeTrans
          (natDivModCountingRemainderIsBounded rightValue (leftPredecessor + 1)
            (natSuccLeSuccOfLe (natZeroLe leftPredecessor)))
          (Nat.le_of_succ_le_succ isBelowFuel)
      match natGcdWithFuelBezout fuel
          (natDivModCounting rightValue (leftPredecessor + 1)).snd
          (leftPredecessor + 1) remainderIsBelowFuel with
      | ⟨remainderCoefficient, baseCoefficient, identityDisjunct⟩ =>
          have regrouped :
              remainderCoefficient *
                  ((leftPredecessor + 1) *
                    (natDivModCounting rightValue (leftPredecessor + 1)).fst) =
                remainderCoefficient *
                    (natDivModCounting rightValue (leftPredecessor + 1)).fst *
                  (leftPredecessor + 1) :=
            (congrArg (remainderCoefficient * ·)
                (Nat.mul_comm (leftPredecessor + 1)
                  (natDivModCounting rightValue (leftPredecessor + 1)).fst)).trans
              (natMulAssoc remainderCoefficient
                (natDivModCounting rightValue (leftPredecessor + 1)).fst
                (leftPredecessor + 1)).symm
          match identityDisjunct with
          | .inl remainderIdentity =>
              ⟨remainderCoefficient *
                  (natDivModCounting rightValue (leftPredecessor + 1)).fst +
                  baseCoefficient,
                remainderCoefficient,
                .inr
                  ((congrArg (remainderCoefficient * ·)
                      (natDivModCountingReconstructs rightValue
                        (leftPredecessor + 1))).trans
                    ((Nat.left_distrib remainderCoefficient
                        ((leftPredecessor + 1) *
                          (natDivModCounting rightValue
                            (leftPredecessor + 1)).fst)
                        (natDivModCounting rightValue
                          (leftPredecessor + 1)).snd).trans
                      ((congrArg
                          (remainderCoefficient *
                              ((leftPredecessor + 1) *
                                (natDivModCounting rightValue
                                  (leftPredecessor + 1)).fst) + ·)
                          remainderIdentity).trans
                        ((Nat.add_assoc
                            (remainderCoefficient *
                              ((leftPredecessor + 1) *
                                (natDivModCounting rightValue
                                  (leftPredecessor + 1)).fst))
                            (baseCoefficient * (leftPredecessor + 1))
                            (natGcdWithFuel fuel
                              (natDivModCounting rightValue
                                (leftPredecessor + 1)).snd
                              (leftPredecessor + 1))).symm.trans
                          ((congrArg
                              (fun regroupedProduct =>
                                regroupedProduct +
                                    baseCoefficient * (leftPredecessor + 1) +
                                  natGcdWithFuel fuel
                                    (natDivModCounting rightValue
                                      (leftPredecessor + 1)).snd
                                    (leftPredecessor + 1))
                              regrouped).trans
                            (congrArg
                              (· +
                                natGcdWithFuel fuel
                                  (natDivModCounting rightValue
                                    (leftPredecessor + 1)).snd
                                  (leftPredecessor + 1))
                              (natRightDistrib
                                (remainderCoefficient *
                                  (natDivModCounting rightValue
                                    (leftPredecessor + 1)).fst)
                                baseCoefficient
                                (leftPredecessor + 1)).symm))))))⟩
          | .inr baseIdentity =>
              ⟨remainderCoefficient *
                  (natDivModCounting rightValue (leftPredecessor + 1)).fst +
                  baseCoefficient,
                remainderCoefficient,
                .inl
                  ((natRightDistrib
                      (remainderCoefficient *
                        (natDivModCounting rightValue
                          (leftPredecessor + 1)).fst)
                      baseCoefficient (leftPredecessor + 1)).trans
                    ((congrArg
                        (remainderCoefficient *
                              (natDivModCounting rightValue
                                (leftPredecessor + 1)).fst *
                            (leftPredecessor + 1) + ·)
                        baseIdentity).trans
                      ((Nat.add_assoc
                          (remainderCoefficient *
                              (natDivModCounting rightValue
                                (leftPredecessor + 1)).fst *
                            (leftPredecessor + 1))
                          (remainderCoefficient *
                            (natDivModCounting rightValue
                              (leftPredecessor + 1)).snd)
                          (natGcdWithFuel fuel
                            (natDivModCounting rightValue
                              (leftPredecessor + 1)).snd
                            (leftPredecessor + 1))).symm.trans
                        ((congrArg
                            (fun regroupedProduct =>
                              regroupedProduct +
                                  remainderCoefficient *
                                    (natDivModCounting rightValue
                                      (leftPredecessor + 1)).snd +
                                natGcdWithFuel fuel
                                  (natDivModCounting rightValue
                                    (leftPredecessor + 1)).snd
                                  (leftPredecessor + 1))
                            regrouped.symm).trans
                          ((congrArg
                              (· +
                                natGcdWithFuel fuel
                                  (natDivModCounting rightValue
                                    (leftPredecessor + 1)).snd
                                  (leftPredecessor + 1))
                              (Nat.left_distrib remainderCoefficient
                                ((leftPredecessor + 1) *
                                  (natDivModCounting rightValue
                                    (leftPredecessor + 1)).fst)
                                (natDivModCounting rightValue
                                  (leftPredecessor + 1)).snd).symm).trans
                            (congrArg
                              (fun reconstructed =>
                                remainderCoefficient * reconstructed +
                                  natGcdWithFuel fuel
                                    (natDivModCounting rightValue
                                      (leftPredecessor + 1)).snd
                                    (leftPredecessor + 1))
                              (natDivModCountingReconstructs rightValue
                                (leftPredecessor + 1)).symm))))))⟩

/-- The Bezout identity at the canonical fuel. -/
theorem natGcdBezout (leftValue rightValue : Nat) :
    NatBezoutIdentityFor (natGcd leftValue rightValue) leftValue rightValue :=
  natGcdWithFuelBezout (leftValue + 1) leftValue rightValue Nat.le.refl

/-- **Greatest-ness**: every common divisor divides the gcd — scale the common
divisor into the Bezout identity and cancel the shared summand.  No second
induction. -/
theorem natDividesGcdOfDividesBoth {commonDivisor leftValue rightValue : Nat}
    (dividesLeft : NatDivides commonDivisor leftValue)
    (dividesRight : NatDivides commonDivisor rightValue) :
    NatDivides commonDivisor (natGcd leftValue rightValue) :=
  match natGcdBezout leftValue rightValue with
  | ⟨leftCoefficient, rightCoefficient, .inl scaledLeftIdentity⟩ =>
      natDividesAddCancelLeft
        (natDividesMulLeft rightCoefficient dividesRight)
        (natDividesOfEq scaledLeftIdentity.symm
          (natDividesMulLeft leftCoefficient dividesLeft))
  | ⟨leftCoefficient, rightCoefficient, .inr scaledRightIdentity⟩ =>
      natDividesAddCancelLeft
        (natDividesMulLeft leftCoefficient dividesLeft)
        (natDividesOfEq scaledRightIdentity.symm
          (natDividesMulLeft rightCoefficient dividesRight))

/-! ## Exact division and Euclid's lemma -/

/-- A positive divisor that divides leaves ZERO remainder in the counting
divider — the divides witness and the divider give two Euclidean
decompositions of the value, and quotient uniqueness collapses the
remainder. -/
theorem natDividesRemainderIsZero {divisor value : Nat}
    (isDivisorPositive : 0 < divisor) (divides : NatDivides divisor value) :
    (natDivModCounting value divisor).snd = 0 :=
  match divides with
  | ⟨quotient, valueEquation⟩ =>
      have decompositionsAgree :
          divisor * quotient + 0 =
            divisor * (natDivModCounting value divisor).fst +
              (natDivModCounting value divisor).snd :=
        valueEquation.symm.trans (natDivModCountingReconstructs value divisor)
      have quotientsAgree :
          quotient = (natDivModCounting value divisor).fst :=
        natEuclideanQuotientUnique isDivisorPositive
          (natDivModCountingRemainderIsBounded value divisor isDivisorPositive)
          decompositionsAgree
      (natAddLeftCancel
        ((congrArg (fun sharedQuotient => divisor * sharedQuotient + 0)
            quotientsAgree).symm.trans
          decompositionsAgree)).symm

/-- **Exact division**: when a positive divisor divides, the counting quotient
reconstructs the value with no remainder term. -/
theorem natExactQuotientReconstructs {divisor value : Nat}
    (isDivisorPositive : 0 < divisor) (divides : NatDivides divisor value) :
    value = divisor * (natDivModCounting value divisor).fst :=
  (natDivModCountingReconstructs value divisor).trans
    (congrArg (divisor * (natDivModCounting value divisor).fst + ·)
      (natDividesRemainderIsZero isDivisorPositive divides))

/-- A right factor of a successor is positive — a zero factor would make the
successor a zero product. -/
theorem natRightFactorOfSuccIsPositive {valuePredecessor divisor quotient : Nat}
    (productEquation : valuePredecessor + 1 = divisor * quotient) :
    0 < quotient :=
  match quotient, productEquation with
  | 0, productEquation => Nat.noConfusion productEquation
  | quotientPredecessor + 1, _ =>
      natSuccLeSuccOfLe (natZeroLe quotientPredecessor)

/-- The exact quotient of a positive value is positive — the normalized
ℚ denominator's positivity supplier. -/
theorem natExactQuotientIsPositive {divisor valuePredecessor : Nat}
    (isDivisorPositive : 0 < divisor)
    (divides : NatDivides divisor (valuePredecessor + 1)) :
    0 < (natDivModCounting (valuePredecessor + 1) divisor).fst :=
  natRightFactorOfSuccIsPositive
    (natExactQuotientReconstructs isDivisorPositive divides)

/-- Coprimality: the gcd collapses to one. -/
def NatCoprime (leftValue rightValue : Nat) : Prop :=
  natGcd leftValue rightValue = 1

/-- **Euclid's lemma**: a divisor coprime to one factor divides the other —
scale the Bezout identity by the surviving factor, note the divisor owns both
the `coefficient * divisor * factor` term and the scaled product, and cancel;
coprimality collapses the leftover `gcd * factor` to the factor. -/
theorem natDividesOfCoprimeOfDividesMul {divisor leftValue rightValue : Nat}
    (isCoprime : NatCoprime divisor leftValue)
    (dividesProduct : NatDivides divisor (leftValue * rightValue)) :
    NatDivides divisor rightValue :=
  have dividesOwnTerm : ∀ scaleCoefficient : Nat,
      NatDivides divisor (scaleCoefficient * divisor * rightValue) :=
    fun scaleCoefficient =>
      natDividesMulRight rightValue
        (natDividesMulLeft scaleCoefficient (natDividesRefl divisor))
  have dividesScaledProduct : ∀ scaleCoefficient : Nat,
      NatDivides divisor (scaleCoefficient * leftValue * rightValue) :=
    fun scaleCoefficient =>
      natDividesOfEq (natMulAssoc scaleCoefficient leftValue rightValue)
        (natDividesMulLeft scaleCoefficient dividesProduct)
  have dividesGcdScaled :
      NatDivides divisor (natGcd divisor leftValue * rightValue) :=
    match natGcdBezout divisor leftValue with
    | ⟨divisorCoefficient, leftCoefficient, .inl identity⟩ =>
        natDividesAddCancelLeft (dividesScaledProduct leftCoefficient)
          (natDividesOfEq
            ((natRightDistrib (leftCoefficient * leftValue)
                (natGcd divisor leftValue) rightValue).symm.trans
              (congrArg (· * rightValue) identity).symm)
            (dividesOwnTerm divisorCoefficient))
    | ⟨divisorCoefficient, leftCoefficient, .inr identity⟩ =>
        natDividesAddCancelLeft (dividesOwnTerm divisorCoefficient)
          (natDividesOfEq
            ((natRightDistrib (divisorCoefficient * divisor)
                (natGcd divisor leftValue) rightValue).symm.trans
              (congrArg (· * rightValue) identity).symm)
            (dividesScaledProduct leftCoefficient))
  natDividesOfEq
    (((Nat.mul_comm 1 rightValue).trans (Nat.zero_add rightValue)).symm.trans
      (congrArg (· * rightValue) isCoprime.symm))
    dividesGcdScaled

/-- A divisor of the quotient scales to a product divisor of the value —
re-associate the witness under the outer factor. -/
theorem natScaledDividesOfDividesQuotient
    {innerDivisor quotient outerFactor value : Nat}
    (divides : NatDivides innerDivisor quotient)
    (factorization : value = outerFactor * quotient) :
    NatDivides (outerFactor * innerDivisor) value :=
  match divides with
  | ⟨cofactor, quotientEquation⟩ =>
      ⟨cofactor,
        factorization.trans
          ((congrArg (outerFactor * ·) quotientEquation).trans
            (natMulAssoc outerFactor innerDivisor cofactor).symm)⟩

/-- A left factor of one is one — the double-successor case refutes through
one injectivity peel. -/
theorem natLeftFactorOfProductEqOne : ∀ {leftFactor rightFactor : Nat},
    leftFactor * rightFactor = 1 → leftFactor = 1
  | 0, rightFactor, productEquation =>
      Nat.noConfusion ((Nat.zero_mul rightFactor).symm.trans productEquation)
  | 1, _, _ => rfl
  | _ + 2, 0, productEquation => Nat.noConfusion productEquation
  | _ + 2, _ + 1, productEquation =>
      Nat.noConfusion (Nat.succ.inj productEquation)

/-- **Dividing out the gcd leaves coprime quotients** — a common divisor of
the exact quotients scales to a common divisor of the originals, hence
divides the gcd itself; cancelling the positive gcd through Euclidean
quotient uniqueness forces it to one. -/
theorem natGcdOfExactQuotientsIsOne {leftValue rightValue : Nat}
    (gcdIsPositive : 0 < natGcd leftValue rightValue) :
    natGcd
        (natDivModCounting leftValue (natGcd leftValue rightValue)).fst
        (natDivModCounting rightValue (natGcd leftValue rightValue)).fst =
      1 :=
  have scaledDividesLeft :
      NatDivides
        (natGcd leftValue rightValue *
          natGcd
            (natDivModCounting leftValue (natGcd leftValue rightValue)).fst
            (natDivModCounting rightValue (natGcd leftValue rightValue)).fst)
        leftValue :=
    natScaledDividesOfDividesQuotient
      (natGcdDividesLeft
        (natDivModCounting leftValue (natGcd leftValue rightValue)).fst
        (natDivModCounting rightValue (natGcd leftValue rightValue)).fst)
      (natExactQuotientReconstructs gcdIsPositive
        (natGcdDividesLeft leftValue rightValue))
  have scaledDividesRight :
      NatDivides
        (natGcd leftValue rightValue *
          natGcd
            (natDivModCounting leftValue (natGcd leftValue rightValue)).fst
            (natDivModCounting rightValue (natGcd leftValue rightValue)).fst)
        rightValue :=
    natScaledDividesOfDividesQuotient
      (natGcdDividesRight
        (natDivModCounting leftValue (natGcd leftValue rightValue)).fst
        (natDivModCounting rightValue (natGcd leftValue rightValue)).fst)
      (natExactQuotientReconstructs gcdIsPositive
        (natGcdDividesRight leftValue rightValue))
  match natDividesGcdOfDividesBoth scaledDividesLeft scaledDividesRight with
  | ⟨cofactor, gcdEquation⟩ =>
      have decompositionsAgree :
          natGcd leftValue rightValue *
              (natGcd
                  (natDivModCounting leftValue
                    (natGcd leftValue rightValue)).fst
                  (natDivModCounting rightValue
                    (natGcd leftValue rightValue)).fst *
                cofactor) +
              0 =
            natGcd leftValue rightValue * 1 + 0 :=
        ((natMulAssoc (natGcd leftValue rightValue)
              (natGcd
                (natDivModCounting leftValue
                  (natGcd leftValue rightValue)).fst
                (natDivModCounting rightValue
                  (natGcd leftValue rightValue)).fst)
              cofactor).symm.trans
          gcdEquation.symm).trans
          (Nat.zero_add (natGcd leftValue rightValue)).symm
      natLeftFactorOfProductEqOne
        (natEuclideanQuotientUnique gcdIsPositive gcdIsPositive
          decompositionsAgree)

/-! ## Divisibility antisymmetry and gcd commutativity — the uniqueness suppliers

Mutual divisibility pins values EQUAL, subtraction-free: composing the two
witnesses gives `divisor * (quotient * cofactor) = divisor`, the two Euclidean
decompositions `divisor * (quotient * cofactor) + 0 = divisor * 1 + 0` agree, so
quotient uniqueness plus the factor-of-one lemma collapse the composite witness.
Commutativity of the (asymmetric, fuel-structural) gcd then falls out of
greatest-ness alone — each orientation's gcd divides the other's, no second
induction. -/

/-- **Antisymmetry of divisibility** — mutual divisors are equal.  The zero
divisor forces the value to zero through its witness; a positive divisor rides
the two-decompositions trick. -/
theorem natDividesAntisymm : ∀ {divisor value : Nat},
    NatDivides divisor value → NatDivides value divisor → divisor = value
  | 0, _, ⟨quotient, valueEquation⟩, _ =>
      (valueEquation.trans (Nat.zero_mul quotient)).symm
  | divisorPredecessor + 1, value, ⟨quotient, valueEquation⟩,
    ⟨cofactor, divisorEquation⟩ =>
      have productCollapses :
          (divisorPredecessor + 1) * (quotient * cofactor) =
            divisorPredecessor + 1 :=
        ((natMulAssoc (divisorPredecessor + 1) quotient cofactor).symm.trans
          (congrArg (· * cofactor) valueEquation.symm)).trans
          divisorEquation.symm
      have decompositionsAgree :
          (divisorPredecessor + 1) * (quotient * cofactor) + 0 =
            (divisorPredecessor + 1) * 1 + 0 :=
        productCollapses.trans (Nat.zero_add (divisorPredecessor + 1)).symm
      have divisorIsPositive : 0 < divisorPredecessor + 1 :=
        natSuccLeSuccOfLe (natZeroLe divisorPredecessor)
      have quotientIsOne : quotient = 1 :=
        natLeftFactorOfProductEqOne
          (natEuclideanQuotientUnique divisorIsPositive divisorIsPositive
            decompositionsAgree)
      ((valueEquation.trans
          (congrArg ((divisorPredecessor + 1) * ·) quotientIsOne)).trans
        (Nat.zero_add (divisorPredecessor + 1))).symm

/-- **The gcd is commutative** — each orientation's gcd divides both arguments,
hence divides the other orientation's gcd by greatest-ness; antisymmetry closes.
No induction on the fuel recursion at all. -/
theorem natGcdComm (leftValue rightValue : Nat) :
    natGcd leftValue rightValue = natGcd rightValue leftValue :=
  natDividesAntisymm
    (natDividesGcdOfDividesBoth (natGcdDividesRight leftValue rightValue)
      (natGcdDividesLeft leftValue rightValue))
    (natDividesGcdOfDividesBoth (natGcdDividesRight rightValue leftValue)
      (natGcdDividesLeft rightValue leftValue))

end FX1Poly.ComputerAlgebra
