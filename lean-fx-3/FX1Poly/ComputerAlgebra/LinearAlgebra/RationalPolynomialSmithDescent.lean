import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithFixedPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # RationalPolynomialSmithDescent — the ℚ[x] degree-multiplicativity lever and re-pivot descent core

`RationalPolynomialSmithFixedPoint` shipped the reduced cross but left the all-zero cross open, pinning the
missing lever: `rpxMul` degree additivity. This module supplies it. `rsdDegreeMul` proves `rpxDegree (p × q) =
rpxDegree p + rpxDegree q` for trim-nonzero factors, from the leading-coefficient product law over the field
ℚ: the product's top coefficient is the product of the two leading coefficients (`rsdMulCoeffTop`), nonzero
over ℚ by the integral-domain law `rsdQnfMulNeZero` (no zero divisors in a field, from `qnfInvMulCancels`),
while everything past the top vanishes (`rsdMulCoeffVanishAbove`), so the trimmed length is exactly
`deg + deg + 1`.

The re-pivot descent core follows: a nonzero pivot-multiple has degree `≥` the pivot
(`rsdMultipleDegreeGePivot`) and a nonzero residue is strictly below the pivot (`rsdResidueBelowPivotWhenNonzero`,
from `rbzClearEntryReducesDegree`), so a re-pivot strictly decreases the minimum pivot degree (`rsdMinDegreeOver`)
— the descent's termination measure. The full re-pivot driver and the all-zero cross it reaches are supplied
downstream in `RationalPolynomialSmithDriver` (`rseHasAllZeroCrossViaRepivot`); the full Smith normal form is
walled (`rsiHasSmithNormalForm`).

Every coefficient lemma is structural on the coefficient list with full `Nat` case enumeration; arithmetic
routes through the shipped `qnf*` field laws and the calibrated-clean core `Nat` order lemmas. No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or `WellFounded.fix`.
Per-declaration audit twin in the matching `FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The integral-domain law over the field ℚ -/

/-- **No zero divisors over ℚ.**  `leftValue ≠ 0 → rightValue ≠ 0 → leftValue · rightValue ≠ 0`.  Were the
product zero, cancelling `leftValue` by its inverse (`qnfInvMulCancels`) would force `rightValue = 0`. -/
theorem rsdQnfMulNeZero {leftValue rightValue : QnfRat}
    (leftNonzero : leftValue ≠ qnfZero) (rightNonzero : rightValue ≠ qnfZero) :
    qnfMul leftValue rightValue ≠ qnfZero := by
  intro productZero
  apply rightNonzero
  calc rightValue
      = qnfMul qnfOne rightValue := (qnfMulOneLeft rightValue).symm
    _ = qnfMul (qnfMul (qnfInv leftValue) leftValue) rightValue :=
          congrArg (qnfMul · rightValue) (qnfInvMulCancels leftNonzero).symm
    _ = qnfMul (qnfInv leftValue) (qnfMul leftValue rightValue) :=
          qnfMulAssoc (qnfInv leftValue) leftValue rightValue
    _ = qnfMul (qnfInv leftValue) qnfZero := congrArg (qnfMul (qnfInv leftValue)) productZero
    _ = qnfZero := qnfMulZeroRight (qnfInv leftValue)

/-! ## The all-zero left factor annihilates the product coefficientwise -/

/-- **A shifted vanishing polynomial vanishes.**  If `poly` reads `qnfZero` at every position, so does
`qnfZero :: poly`. -/
theorem rsdConsZeroVanish (poly : List QnfRat) (allZero : ∀ index, rpxCoeff poly index = qnfZero) :
    ∀ position : Nat, rpxCoeff (qnfZero :: poly) position = qnfZero
  | 0 => rfl
  | priorPosition + 1 => allZero priorPosition

/-- **A vanishing left factor makes the whole product vanish coefficientwise.**  If `leftPoly` reads
`qnfZero` at every position then `rpxCoeff (leftPoly × rightPoly) position = qnfZero`.  Structural on
`leftPoly`: the head is `qnfZero` (so the leading scale summand dies), the shifted tail recurses. -/
theorem rsdMulCoeffZeroOfLeftZero (rightPoly : List QnfRat) :
    ∀ (leftPoly : List QnfRat), (∀ index, rpxCoeff leftPoly index = qnfZero) →
      ∀ position : Nat, rpxCoeff (rpxMul leftPoly rightPoly) position = qnfZero
  | [], _, _ => rfl
  | headCoeff :: tailCoeffs, leftZero, position => by
      have headZero : headCoeff = qnfZero := leftZero 0
      show rpxCoeff (rpxAdd (rpxScale headCoeff rightPoly)
          (qnfZero :: rpxMul tailCoeffs rightPoly)) position = qnfZero
      rw [rpxCoeffAdd, rpxCoeffScale, headZero, qnfMulZeroLeft, qnfAddZeroLeft]
      cases position with
      | zero => rfl
      | succ priorPosition =>
          exact rsdMulCoeffZeroOfLeftZero rightPoly tailCoeffs
            (fun index => leftZero (index + 1)) priorPosition

/-! ## T1 — the leading-coefficient product and the vanishing above -/

/-- **The product's top coefficient is the product of the leading coefficients.**  For factors that vanish
strictly above their degrees, `rpxCoeff (leftPoly × rightPoly) (degLeft + degRight) = (rpxCoeff leftPoly
degLeft)·(rpxCoeff rightPoly degRight)`.  Structural on `leftPoly`, casing `degLeft`: the `degLeft = 0` case
(a nonzero constant head, all-zero tail) reads the head against `rightPoly`'s top; the successor case reads
`rightPoly` above its degree (vanishes) on the leading summand and recurses on the shifted tail. -/
theorem rsdMulCoeffTop (rightPoly : List QnfRat) (degRight : Nat)
    (rightVanishes : ∀ index, degRight < index → rpxCoeff rightPoly index = qnfZero) :
    ∀ (leftPoly : List QnfRat) (degLeft : Nat),
      (∀ index, degLeft < index → rpxCoeff leftPoly index = qnfZero) →
      rpxCoeff (rpxMul leftPoly rightPoly) (degLeft + degRight)
        = qnfMul (rpxCoeff leftPoly degLeft) (rpxCoeff rightPoly degRight)
  | [], degLeft, _ => by
      show rpxCoeff (rpxMul [] rightPoly) (degLeft + degRight)
          = qnfMul (rpxCoeff [] degLeft) (rpxCoeff rightPoly degRight)
      exact (qnfMulZeroLeft (rpxCoeff rightPoly degRight)).symm
  | headCoeff :: tailCoeffs, degLeft, leftVanishes => by
      cases degLeft with
      | zero =>
          have tailAllZero : ∀ index, rpxCoeff tailCoeffs index = qnfZero :=
            fun index => leftVanishes (index + 1) (Nat.succ_pos index)
          show rpxCoeff (rpxAdd (rpxScale headCoeff rightPoly)
              (qnfZero :: rpxMul tailCoeffs rightPoly)) (0 + degRight)
            = qnfMul headCoeff (rpxCoeff rightPoly degRight)
          rw [rpxCoeffAdd, rpxCoeffScale,
            rsdConsZeroVanish (rpxMul tailCoeffs rightPoly)
              (rsdMulCoeffZeroOfLeftZero rightPoly tailCoeffs tailAllZero) (0 + degRight),
            qnfAddZeroRight, Nat.zero_add]
      | succ priorDegLeft =>
          have rightTopZero : rpxCoeff rightPoly (Nat.succ (priorDegLeft + degRight)) = qnfZero :=
            rightVanishes (Nat.succ (priorDegLeft + degRight))
              (Nat.lt_succ_of_le (Nat.le_add_left degRight priorDegLeft))
          show rpxCoeff (rpxMul (headCoeff :: tailCoeffs) rightPoly) (Nat.succ priorDegLeft + degRight)
            = qnfMul (rpxCoeff tailCoeffs priorDegLeft) (rpxCoeff rightPoly degRight)
          rw [Nat.succ_add]
          show rpxCoeff (rpxAdd (rpxScale headCoeff rightPoly)
              (qnfZero :: rpxMul tailCoeffs rightPoly)) (Nat.succ (priorDegLeft + degRight))
            = qnfMul (rpxCoeff tailCoeffs priorDegLeft) (rpxCoeff rightPoly degRight)
          rw [rpxCoeffAdd, rpxCoeffScale, rightTopZero, qnfMulZeroRight, qnfAddZeroLeft]
          show rpxCoeff (rpxMul tailCoeffs rightPoly) (priorDegLeft + degRight)
            = qnfMul (rpxCoeff tailCoeffs priorDegLeft) (rpxCoeff rightPoly degRight)
          exact rsdMulCoeffTop rightPoly degRight rightVanishes tailCoeffs priorDegLeft
            (fun index indexAbove => leftVanishes (index + 1) (Nat.succ_lt_succ indexAbove))

/-- **The product vanishes strictly above the sum of degrees.**  For factors that vanish strictly above
their degrees, `degLeft + degRight < position ⟹ rpxCoeff (leftPoly × rightPoly) position = qnfZero`.
Structural on `leftPoly`, casing `degLeft`: `degLeft = 0` uses the all-zero tail; the successor case reads
`rightPoly` above its degree on the leading summand and recurses on the shifted tail. -/
theorem rsdMulCoeffVanishAbove (rightPoly : List QnfRat) (degRight : Nat)
    (rightVanishes : ∀ index, degRight < index → rpxCoeff rightPoly index = qnfZero) :
    ∀ (leftPoly : List QnfRat) (degLeft : Nat),
      (∀ index, degLeft < index → rpxCoeff leftPoly index = qnfZero) →
      ∀ position : Nat, degLeft + degRight < position →
        rpxCoeff (rpxMul leftPoly rightPoly) position = qnfZero
  | [], _, _, _, _ => rfl
  | headCoeff :: tailCoeffs, degLeft, leftVanishes, position, positionAbove => by
      cases degLeft with
      | zero =>
          have tailAllZero : ∀ index, rpxCoeff tailCoeffs index = qnfZero :=
            fun index => leftVanishes (index + 1) (Nat.succ_pos index)
          show rpxCoeff (rpxAdd (rpxScale headCoeff rightPoly)
              (qnfZero :: rpxMul tailCoeffs rightPoly)) position = qnfZero
          rw [rpxCoeffAdd, rpxCoeffScale,
            rightVanishes position (Nat.lt_of_le_of_lt (Nat.le_add_left degRight 0) positionAbove),
            qnfMulZeroRight, qnfAddZeroLeft,
            rsdConsZeroVanish (rpxMul tailCoeffs rightPoly)
              (rsdMulCoeffZeroOfLeftZero rightPoly tailCoeffs tailAllZero) position]
      | succ priorDegLeft =>
          have rightZeroAtPos : rpxCoeff rightPoly position = qnfZero :=
            rightVanishes position
              (Nat.lt_of_le_of_lt (Nat.le_add_left degRight (Nat.succ priorDegLeft)) positionAbove)
          show rpxCoeff (rpxAdd (rpxScale headCoeff rightPoly)
              (qnfZero :: rpxMul tailCoeffs rightPoly)) position = qnfZero
          rw [rpxCoeffAdd, rpxCoeffScale, rightZeroAtPos, qnfMulZeroRight, qnfAddZeroLeft]
          cases position with
          | zero => rfl
          | succ priorPosition =>
              show rpxCoeff (rpxMul tailCoeffs rightPoly) priorPosition = qnfZero
              rw [Nat.succ_add] at positionAbove
              exact rsdMulCoeffVanishAbove rightPoly degRight rightVanishes tailCoeffs priorDegLeft
                (fun index indexAbove => leftVanishes (index + 1) (Nat.succ_lt_succ indexAbove))
                priorPosition (Nat.lt_of_succ_lt_succ positionAbove)

/-- **T1 — THE LEVER: `rpxMul` degree additivity over ℚ.**  For trim-nonzero factors, `rpxDegree (leftPoly ×
rightPoly) = rpxDegree leftPoly + rpxDegree rightPoly`.  The product's top coefficient (`rsdMulCoeffTop`) is
the product of the two nonzero leading coefficients, hence nonzero over the field ℚ (`rsdQnfMulNeZero`), so
the trimmed length is bounded ABOVE by `deg+deg+1` (nothing survives past the top, `rsdMulCoeffVanishAbove`
through `rpdTrimLengthLeOfVanishFrom`) and BELOW by `deg+deg+1` (the top coefficient is nonzero, so the
trimmed length exceeds `deg+deg`).  Antisymmetry pins the trimmed length exactly, and `deg = length − 1`. -/
theorem rsdDegreeMul (leftPoly rightPoly : List QnfRat)
    (leftNonzero : rpxTrim leftPoly ≠ [])
    (rightNonzero : rpxTrim rightPoly ≠ []) :
    rpxDegree (rpxMul leftPoly rightPoly) = rpxDegree leftPoly + rpxDegree rightPoly := by
  have leftVanishes : ∀ index, rpxDegree leftPoly < index → rpxCoeff leftPoly index = qnfZero := by
    intro index indexAbove
    apply rpxCoeffZeroFromTrimLength
    rw [rpxTrimLengthEqDegreeSucc leftPoly leftNonzero]
    exact indexAbove
  have rightVanishes : ∀ index, rpxDegree rightPoly < index → rpxCoeff rightPoly index = qnfZero := by
    intro index indexAbove
    apply rpxCoeffZeroFromTrimLength
    rw [rpxTrimLengthEqDegreeSucc rightPoly rightNonzero]
    exact indexAbove
  have productVanishes : ∀ index, rpxDegree leftPoly + rpxDegree rightPoly < index →
      rpxCoeff (rpxMul leftPoly rightPoly) index = qnfZero :=
    rsdMulCoeffVanishAbove rightPoly (rpxDegree rightPoly) rightVanishes leftPoly (rpxDegree leftPoly)
      leftVanishes
  have topCoeff : rpxCoeff (rpxMul leftPoly rightPoly) (rpxDegree leftPoly + rpxDegree rightPoly)
      = qnfMul (rpxCoeff leftPoly (rpxDegree leftPoly)) (rpxCoeff rightPoly (rpxDegree rightPoly)) :=
    rsdMulCoeffTop rightPoly (rpxDegree rightPoly) rightVanishes leftPoly (rpxDegree leftPoly) leftVanishes
  have topNonzero : rpxCoeff (rpxMul leftPoly rightPoly) (rpxDegree leftPoly + rpxDegree rightPoly)
      ≠ qnfZero := by
    rw [topCoeff]
    exact rsdQnfMulNeZero
      (rpxCoeffAtDegreeNonzeroWhenNonempty leftPoly leftNonzero)
      (rpxCoeffAtDegreeNonzeroWhenNonempty rightPoly rightNonzero)
  have upperBound : (rpxTrim (rpxMul leftPoly rightPoly)).length
      ≤ rpxDegree leftPoly + rpxDegree rightPoly + 1 :=
    rpdTrimLengthLeOfVanishFrom (rpxMul leftPoly rightPoly)
      (rpxDegree leftPoly + rpxDegree rightPoly + 1)
      (fun index indexBound => productVanishes index indexBound)
  have lowerBound : rpxDegree leftPoly + rpxDegree rightPoly + 1
      ≤ (rpxTrim (rpxMul leftPoly rightPoly)).length := by
    cases Nat.lt_or_ge (rpxDegree leftPoly + rpxDegree rightPoly)
        (rpxTrim (rpxMul leftPoly rightPoly)).length with
    | inl isBelow => exact isBelow
    | inr isLengthLe =>
        exact absurd
          (rpxCoeffZeroFromTrimLength (rpxMul leftPoly rightPoly)
            (rpxDegree leftPoly + rpxDegree rightPoly) isLengthLe)
          topNonzero
  have lengthEq : (rpxTrim (rpxMul leftPoly rightPoly)).length
      = rpxDegree leftPoly + rpxDegree rightPoly + 1 :=
    Nat.le_antisymm upperBound lowerBound
  calc rpxDegree (rpxMul leftPoly rightPoly)
      = (rpxTrim (rpxMul leftPoly rightPoly)).length - 1 := rfl
    _ = rpxDegree leftPoly + rpxDegree rightPoly + 1 - 1 := by rw [lengthEq]
    _ = rpxDegree leftPoly + rpxDegree rightPoly := rfl

/-! ## T2 — the re-pivot descent core -/

/-- **A nonzero product has a nonzero left factor.**  Contrapositive of `rsdMulCoeffZeroOfLeftZero`: were
`cofactor` the zero polynomial, the whole product would trim to `[]`. -/
theorem rsdCofactorNonzeroOfProductNonzero (cofactor pivot : List QnfRat)
    (productNonzero : rpxTrim (rpxMul cofactor pivot) ≠ []) : rpxTrim cofactor ≠ [] := by
  intro cofactorTrimNil
  apply productNonzero
  apply rpdTrimNilOfAllCoeffsZero
  intro position
  exact rsdMulCoeffZeroOfLeftZero pivot cofactor
    (fun index => rpdCoeffZeroOfTrimNil cofactor index cofactorTrimNil) position

/-- **T2 — a nonzero pivot-multiple has degree `≥` the pivot's** (T1-powered).  `rpxDegree pivot ≤ rpxDegree
(cofactor × pivot)` for a nonzero pivot and a nonzero product — a pivot can never be replaced by a
strictly-smaller-degree MULTIPLE of itself.  Direct from `rsdDegreeMul` plus `Nat.le_add_left`. -/
theorem rsdMultipleDegreeGePivot (cofactor pivot : List QnfRat)
    (pivotNonzero : rpxTrim pivot ≠ [])
    (productNonzero : rpxTrim (rpxMul cofactor pivot) ≠ []) :
    rpxDegree pivot ≤ rpxDegree (rpxMul cofactor pivot) := by
  have cofactorNonzero : rpxTrim cofactor ≠ [] :=
    rsdCofactorNonzeroOfProductNonzero cofactor pivot productNonzero
  rw [rsdDegreeMul cofactor pivot cofactorNonzero pivotNonzero]
  exact Nat.le_add_left (rpxDegree pivot) (rpxDegree cofactor)

/-- **T2 — a nonzero residue is strictly below the pivot.**  When `rsmClearAgainst pivot entry` (the residue
`entry mod pivot`) does not annihilate, its degree is strictly below the pivot's — so swapping it into the
pivot slot strictly drops the pivot degree, the descent measure of the re-pivot.  Direct from the committed
`rbzClearEntryReducesDegree` (`= rpdDivModRemainderDegree`). -/
theorem rsdResidueBelowPivotWhenNonzero (pivot entry : List QnfRat)
    (pivotNonzero : rpxTrim pivot ≠ [])
    (residueNonzero : rpxTrim (rsmClearAgainst pivot entry) ≠ []) :
    rpxDegree (rsmClearAgainst pivot entry) < rpxDegree pivot :=
  (rbzClearEntryReducesDegree pivot entry pivotNonzero).resolve_left residueNonzero

/-- Degree of a nonzero entry, or `fallback` for the zero polynomial. -/
def rsdEntryDegreeOr (fallback : Nat) (entry : List QnfRat) : Nat :=
  match rpxTrim entry with
  | [] => fallback
  | _ :: _ => rpxDegree entry

/-- **The min-degree cross measure.**  The minimum `rpxDegree` over the nonzero entries of a list of cross
entries (zero entries skipped); `fallback` seeds the fold and is returned when every entry is zero.  A
re-pivot swaps the achieving nonzero entry into the pivot slot and re-clears, strictly decreasing this
measure via `rsdResidueBelowPivotWhenNonzero` (the residues drop below the achieving pivot degree). -/
def rsdMinDegreeOver (fallback : Nat) : List (List QnfRat) → Nat
  | [] => fallback
  | entry :: rest =>
      match rpxTrim entry with
      | [] => rsdMinDegreeOver fallback rest
      | _ :: _ => Nat.min (rpxDegree entry) (rsdMinDegreeOver fallback rest)

/-! ## Groundings (fires)

Closed-value kernel pins; the convolution / degree pipeline reduces to canonical `QnfRat` normal forms, so
the concrete-value fires are `rfl`, and the theorem instantiations discharge on the nonzero-trim witnesses. -/

set_option maxRecDepth 8192

/-- `x + 2 = [2, 1]` is a nonzero polynomial. -/
theorem rsdFireLinearPlusTwoNonzero : rpxTrim [qnfOfInt 2, qnfOfInt 1] ≠ [] := by
  rw [show rpxTrim [qnfOfInt 2, qnfOfInt 1] = [qnfOfInt 2, qnfOfInt 1] from rfl]
  exact List.cons_ne_nil (qnfOfInt 2) [qnfOfInt 1]

/-- `x − 1 = [-1, 1]` is a nonzero polynomial. -/
theorem rsdFireLinearMinusOneNonzero : rpxTrim [qnfOfInt (-1), qnfOfInt 1] ≠ [] := by
  rw [show rpxTrim [qnfOfInt (-1), qnfOfInt 1] = [qnfOfInt (-1), qnfOfInt 1] from rfl]
  exact List.cons_ne_nil (qnfOfInt (-1)) [qnfOfInt 1]

/-- `x² + 1 = [1, 0, 1]` is a nonzero polynomial. -/
theorem rsdFireSquarePlusOneNonzero : rpxTrim [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1] ≠ [] := by
  rw [show rpxTrim [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1] = [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1] from rfl]
  exact List.cons_ne_nil (qnfOfInt 1) [qnfOfInt 0, qnfOfInt 1]

/-- `x = [0, 1]` is a nonzero polynomial. -/
theorem rsdFireMonomialXNonzero : rpxTrim [qnfOfInt 0, qnfOfInt 1] ≠ [] := by
  rw [show rpxTrim [qnfOfInt 0, qnfOfInt 1] = [qnfOfInt 0, qnfOfInt 1] from rfl]
  exact List.cons_ne_nil (qnfOfInt 0) [qnfOfInt 1]

/-- Fire (T1 theorem): `(x + 2)(x − 1)` has degree `deg(x+2) + deg(x−1)` via `rsdDegreeMul`. -/
theorem rsdFireDegreeMulLinearTimesLinearTheorem :
    rpxDegree (rpxMul [qnfOfInt 2, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1])
      = rpxDegree [qnfOfInt 2, qnfOfInt 1] + rpxDegree [qnfOfInt (-1), qnfOfInt 1] :=
  rsdDegreeMul [qnfOfInt 2, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]
    rsdFireLinearPlusTwoNonzero rsdFireLinearMinusOneNonzero

/-- Fire (T1 value): `(x + 2)(x − 1) = x² + x − 2` has degree `2`. -/
theorem rsdFireDegreeMulLinearTimesLinearValue :
    rpxDegree (rpxMul [qnfOfInt 2, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]) = 2 := rfl

/-- Fire (T1 theorem): `(x² + 1)·x` has degree `deg(x²+1) + deg(x)` via `rsdDegreeMul`. -/
theorem rsdFireDegreeMulSquareTimesMonomialTheorem :
    rpxDegree (rpxMul [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1] [qnfOfInt 0, qnfOfInt 1])
      = rpxDegree [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1] + rpxDegree [qnfOfInt 0, qnfOfInt 1] :=
  rsdDegreeMul [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1] [qnfOfInt 0, qnfOfInt 1]
    rsdFireSquarePlusOneNonzero rsdFireMonomialXNonzero

/-- Fire (T1 value): `(x² + 1)·x = x³ + x` has degree `3`. -/
theorem rsdFireDegreeMulSquareTimesMonomialValue :
    rpxDegree (rpxMul [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1] [qnfOfInt 0, qnfOfInt 1]) = 3 := rfl

/-- Fire (T2 multiple degree): the nonzero pivot-multiple `(x + 1)(x − 1) = x² − 1` has degree
`≥ deg(x − 1) = 1` — a pivot can never be replaced by a smaller-degree multiple. -/
theorem rsdFireMultipleDegreeGe :
    rpxDegree [qnfOfInt (-1), qnfOfInt 1]
      ≤ rpxDegree (rpxMul [qnfOfInt 1, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]) :=
  rsdMultipleDegreeGePivot [qnfOfInt 1, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]
    rsdFireLinearMinusOneNonzero
    (by
      rw [show rpxTrim (rpxMul [qnfOfInt 1, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1])
            = [qnfNeg qnfOne, qnfZero, qnfOne] from rfl]
      exact List.cons_ne_nil (qnfNeg qnfOne) [qnfZero, qnfOne])

/-- Fire (T2 residue below pivot, value): `(x² + 1) mod (x − 1) = 2` has degree `0 < 1 = deg(x − 1)`. -/
theorem rsdFireResidueBelowPivotValue :
    rpxDegree (rsmClearAgainst [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]) = 0 := rfl

/-- Fire (T2 residue below pivot, theorem): the nonzero residue `(x² + 1) mod (x − 1)` is strictly below the
pivot `x − 1` via `rsdResidueBelowPivotWhenNonzero`. -/
theorem rsdFireResidueBelowPivotTheorem :
    rpxDegree (rsmClearAgainst [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1])
      < rpxDegree [qnfOfInt (-1), qnfOfInt 1] :=
  rsdResidueBelowPivotWhenNonzero [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]
    rsdFireLinearMinusOneNonzero
    (by
      rw [show rpxTrim (rsmClearAgainst [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1])
            = [qnfOfInt 2] from rfl]
      exact List.cons_ne_nil (qnfOfInt 2) [])

/-- Fire (min-degree measure): the off-pivot cross entries `x + 1` and `x − 1` of the fire matrix about the
pivot `(1, 1)` both have degree `1`, so the min-degree measure is `1`. -/
theorem rsdFireMinDegreeOverCross :
    rsdMinDegreeOver 99 [[qnfOfInt 1, qnfOfInt 1], [qnfOfInt (-1), qnfOfInt 1]] = 1 := rfl

/-! ## Content marker -/

/-- ℚ[x] `rpxMul` degree additivity is decided: `rpxDegree (p × q) = rpxDegree p + rpxDegree q` for trim-nonzero
factors (`rsdDegreeMul`), from the leading-coefficient product law (`rsdMulCoeffTop`), the integral-domain law
(`rsdQnfMulNeZero`), and vanishing above the top (`rsdMulCoeffVanishAbove`). The re-pivot descent core follows:
a nonzero pivot-multiple has degree `≥` the pivot (`rsdMultipleDegreeGePivot`) and a nonzero residue is strictly
below it (`rsdResidueBelowPivotWhenNonzero`), so a re-pivot strictly decreases the min pivot degree
(`rsdMinDegreeOver`). The full re-pivot driver and its all-zero cross are decided downstream
(`rseHasAllZeroCrossViaRepivot`); the full Smith normal form is walled (`rsiHasSmithNormalForm`). -/
def rsdHasDegreeMultiplicativity : Bool := true

end FX1Poly.ComputerAlgebra
