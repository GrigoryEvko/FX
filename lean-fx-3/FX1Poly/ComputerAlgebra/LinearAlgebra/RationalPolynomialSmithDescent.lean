import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialSmithFixedPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithDescent — the ℚ[x] degree-multiplicativity
lever and the Smith re-pivot descent core

The committed ℚ[x] Smith cross fixed point (`RationalPolynomialSmithFixedPoint`) shipped the REDUCED cross
(every off-pivot cross entry below the pivot) but WALLED the ALL-ZERO cross owner-false
(`rsfHasAllZeroCrossFixedPoint := false`).  Its docstring pinned the exact missing lever: `rpxMul` DEGREE
ADDITIVITY (`rpxDegree (p × q) = rpxDegree p + rpxDegree q` for nonzero `p`, `q`), which turns "a nonzero
pivot-multiple has degree `≥ deg pivot`" into "a nonzero non-divisible residue strictly drops the min pivot
degree", the termination measure of the textbook Smith RE-PIVOT.  This module supplies exactly that lever
and the re-pivot descent core.

## T1 — THE LEVER (`rsdDegreeMul`)

`rpxDegree (rpxMul leftPoly rightPoly) = rpxDegree leftPoly + rpxDegree rightPoly` for trim-nonzero factors,
proved from the leading-coefficient product law over the FIELD ℚ.  Two coefficient lemmas, both by structural
induction on the LEFT factor, feed the degree equation:

  * **Top coefficient** (`rsdMulCoeffTop`): `rpxCoeff (leftPoly × rightPoly) (degLeft + degRight) =
    (leadLeft)·(leadRight)`.  The `rpxMul` convolution's top term is the product of the two leading
    coefficients — every other contribution to that position reads a factor coefficient above its degree,
    which vanishes.
  * **Vanishing above** (`rsdMulCoeffVanishAbove`): `degLeft + degRight < position ⟹ rpxCoeff (leftPoly ×
    rightPoly) position = qnfZero` — no convolution term survives past the top.

Over ℚ the product of two nonzero leading coefficients is nonzero (the integral-domain law `rsdQnfMulNeZero`,
derived from `qnfInvMulCancels` — no zero divisors in a field), so the top coefficient is nonzero and the
trimmed length is EXACTLY `degLeft + degRight + 1`, i.e. the degree is the sum.  This is the capability the
committed kit's degree module explicitly lacked.

## T2 — the re-pivot descent core

  * `rsdMultipleDegreeGePivot` (T1-powered): a nonzero `pivot`-multiple `cofactor × pivot` has degree
    `≥ deg pivot` — the fact that a pivot cannot be replaced by a smaller-degree MULTIPLE of itself.
  * `rsdResidueBelowPivotWhenNonzero` (committed `rbzClearEntryReducesDegree`): a nonzero residue
    `rsmClearAgainst pivot entry` (the entry the pivot does NOT divide) has degree strictly below the pivot's
    — so swapping it into the pivot slot strictly drops the pivot degree.
  * `rsdMinDegreeOver` — the min-degree measure over a list of cross entries (zero entries skipped).

Together these are the descent's termination content: a re-pivot strictly decreases the minimum pivot degree.

## The honest walls

The FULL re-pivot DRIVER — swap the smaller-degree residue into the pivot slot, re-clear about the MOVING
position, and iterate with structural `Nat` fuel = the min-degree measure until the cross is all-zero — needs
the moving-position ARITY bookkeeping (tracking which row/column index the pivot now occupies across the swap
and re-index) which is matrix plumbing orthogonal to the degree lever.  Recorded owner-false
(`rsdHasRepivotDriver := false`); the all-zero cross fixed point that rests on it is likewise owner-false
(`rsdHasAllZeroCrossViaRepivot := false`).  The committed `rsfHasAllZeroCrossFixedPoint := false` and
`rsmHasCrossFixedPoint := false` stay byte-intact.  The submatrix descent toward the diagonal
invariant-factor chain `d₁ | d₂ | ⋯ | dᵣ` (combining `rpeGcdDividesBoth` with `rbzDividesTrans`) is recorded
owner-false (`rsdHasInvariantFactorChain := false`); the extractor `rsfSubmatrix` already ships.

## Zero-axiom design

Every coefficient lemma is structural on the coefficient list and casing the degree/position with full
`Nat.succ`/`zero` enumeration; arithmetic routes through the shipped `qnf*` field laws (transported to plain
`Eq`) and the calibrated-clean core `Nat` lemmas (`Nat.succ_add`, `Nat.zero_add`, `Nat.lt_succ_of_le`,
`Nat.le_add_left`, `Nat.succ_lt_succ`, `Nat.lt_of_succ_lt_succ`, `Nat.lt_of_le_of_lt`, `Nat.lt_or_ge`,
`Nat.le_antisymm`, `Nat.succ_pos`, `Nat.not_lt_zero`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`, `funext`, or `WellFounded.fix`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/RationalPolynomialSmithDescent.lean`. -/

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

/-! ## Content markers -/

/-- DECIDED (the LEVER the committed `rsfHasAllZeroCrossFixedPoint := false` docstring named as missing):
`rpxMul` DEGREE ADDITIVITY over ℚ — `rpxDegree (leftPoly × rightPoly) = rpxDegree leftPoly + rpxDegree
rightPoly` for trim-nonzero factors (`rsdDegreeMul`).  Proved from the leading-coefficient product law:
the product's top coefficient is the product of the two leading coefficients (`rsdMulCoeffTop`), nonzero over
the field ℚ (`rsdQnfMulNeZero`, the integral-domain law from `qnfInvMulCancels`), while everything past the
top vanishes (`rsdMulCoeffVanishAbove`), so the trimmed length is exactly `deg + deg + 1`. -/
def rsdHasDegreeMultiplicativity : Bool := true

/-- DECIDED: the re-pivot descent CORE — a nonzero pivot-multiple has degree `≥` the pivot
(`rsdMultipleDegreeGePivot`, T1-powered) and a nonzero residue is strictly below the pivot
(`rsdResidueBelowPivotWhenNonzero`, from the committed `rbzClearEntryReducesDegree`).  Together: a re-pivot
(swap the smaller-degree residue into the pivot slot) strictly decreases the minimum pivot degree, the
termination measure `rsdMinDegreeOver`.  This is the descent's termination content, which the committed kit
lacked (no degree multiplicativity). -/
def rsdHasRepivotDescentCore : Bool := true

/-- WALLED (owner-false): the FULL re-pivot DRIVER over ℚ[x]-matrices.  The termination CONTENT is decided
(`rsdHasRepivotDescentCore`): a re-pivot strictly drops the min pivot degree.  What remains is the
moving-position ARITY bookkeeping — after swapping the achieving off-pivot residue into the pivot slot, the
pivot occupies a NEW `(row, col)` and the re-clear must re-index about that moving position, tracking which
entries are now on the cross across the swap.  This is matrix plumbing orthogonal to the degree lever
(structural `Nat` fuel = `rsdMinDegreeOver`, decreasing by `rsdResidueBelowPivotWhenNonzero` each round).
Route: the swap+re-index driver → the per-round strict drop of `rsdMinDegreeOver` → the fuel-adequate
iterate. -/
def rsdHasRepivotDriver : Bool := false

/-- WALLED (owner-false; the committed `rsfHasAllZeroCrossFixedPoint := false` and `rsmHasCrossFixedPoint :=
false` stay byte-intact): the ALL-ZERO cleared cross via the re-pivot driver — every off-pivot cross entry
trims to `[]`, i.e. `rsfCrossDegreeSum` hits `0`.  This rests on the full re-pivot driver
(`rsdHasRepivotDriver`, walled above): iterate the swap+re-clear until no nonzero non-divisible residue
remains, at which point the surviving pivot DIVIDES every cross entry and the residues all annihilate.  The
degree lever (T1) that makes the iteration terminate is DECIDED; only the driver's matrix bookkeeping is
open. -/
def rsdHasAllZeroCrossViaRepivot : Bool := false

/-- WALLED (owner-false; the committed `rsfHasSubmatrixDescent := false` stays byte-intact): the submatrix
descent toward the diagonal invariant-factor chain.  With the all-zero cross (`rsdHasAllZeroCrossViaRepivot`,
walled), the `(r-1)×(c-1)` submatrix extractor `rsfSubmatrix` (already shipped) is the recursion target: (1)
descend on `rsfSubmatrix` with a fresh `Nat` measure = matrix size, producing `diag(d₁, …, dᵣ, 0, …)`; (2)
the divisibility chain `d₁ | d₂ | ⋯ | dᵣ` combining the committed `rpeGcdDividesBoth` (each `dᵢ` is a gcd of
the surviving minors) with `rbzDividesTrans` (transitivity of `rpeDivides`).  Both ingredients ship; the open
part is the diagonalization driver that produces the chain, gated on the all-zero cross. -/
def rsdHasInvariantFactorChain : Bool := false

end FX1Poly.ComputerAlgebra
