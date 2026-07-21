import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomialDegree

/-! # RationalPolynomialRing — the ℚ[x] list-level ring layer, aggregate division reconstruction, and "gcd
divides both"

`RationalPolynomial` shipped Euclidean division with the evaluation-level reconstruction invariant, and
`RationalPolynomialDegree` supplied the remainder degree bound and the exact single-step trim-level
reconstruction. Both left "gcd divides both" open: the aggregate reconstruction `dividend = quotient·divisor +
remainder` as polynomials (not just at each evaluation point) needs `rpxMul` right-distributivity over `rpxAdd`,
which rests on a list-level commutative-ring layer. This module supplies that layer and closes the wall.

Over ascending coefficient lists, `rpxAdd` is commutative/associative/interchanging, `rpxScale` distributes
over polynomial and scalar sums and composes, and `rpxMul` distributes on both sides — all at plain list `Eq`;
`rpxMul` is associative at the trim level (`rpeMulAssocTrim`), the zero-padding of `rpxScale qnfZero` forcing
the trim statement. The aggregate reconstruction `rpeDivModReconstructsTrim`
(`rpxTrim (quotient·divisor + remainder) = rpxTrim dividend` at every fuel) follows by fuel induction using
right-distributivity and the coefficient bridge.

Divisibility is `rpeDivides divisor dividend := ∃ cofactor, rpxTrim (cofactor·divisor) = rpxTrim dividend`.
Zero remainder gives divisibility (`rpeExactDivisionGivesDivides`); a common divisor divides any left-cofactor
combination (`rpeLinearCombinationDivides`); and the Euclidean invariant closes by fuel induction with an
honest fuel-adequacy bound (`rpeGcdDividesBothInvariant`), giving `rpeGcdDividesBoth` at the adequate fuel. The
full Bezout identity is supplied downstream in `RationalPolynomialBezout` (`rbzHasBezoutIdentity`).

Every list/scale/mul law is structural on the coefficient list; every trim-level law routes through the
coefficient bridge and the shipped `qnf*` field laws; the gcd fuel bookkeeping uses only calibrated-clean Nat
order lemmas. No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`,
or `WellFounded.fix`. Per-declaration audit twin in the matching `FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The coefficient bridge (trim equality ⟺ pointwise coefficient equality) -/

/-- **Equal trims read equal coefficients.**  `rpxTrim leftPoly = rpxTrim rightPoly → rpxCoeff leftPoly n =
rpxCoeff rightPoly n`.  The converse of the committed `rpdTrimEqOfCoeffEq`; together they make trim
equality a per-position ℚ equation. -/
theorem rpeCoeffEqOfTrimEq {leftPoly rightPoly : List QnfRat}
    (trimEq : rpxTrim leftPoly = rpxTrim rightPoly) (position : Nat) :
    rpxCoeff leftPoly position = rpxCoeff rightPoly position :=
  (rpxCoeffTrimAgree leftPoly position).symm.trans
    ((congrArg (fun coeffs => rpxCoeff coeffs position) trimEq).trans
      (rpxCoeffTrimAgree rightPoly position))

/-! ## T1a — the `rpxAdd` commutative-monoid layer (plain `Eq`) -/

/-- **`rpxAdd` has a right unit.**  `rpxAdd poly [] = poly` — the trailing empty summand carries the head
polynomial through; needs the head-constructor case split (`rpxAdd _ []` is stuck otherwise). -/
theorem rpeAddNilRight : ∀ poly : List QnfRat, rpxAdd poly [] = poly
  | [] => rfl
  | _ :: _ => rfl

/-- **`rpxAdd` is commutative** at the plain list level — tail padding is symmetric and each coefficient
sum commutes (`qnfAddComm`). -/
theorem rpeAddComm : ∀ leftPoly rightPoly : List QnfRat,
    rpxAdd leftPoly rightPoly = rpxAdd rightPoly leftPoly
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | leftHead :: leftTail, rightHead :: rightTail =>
      (congrArg (· :: rpxAdd leftTail rightTail) (qnfAddComm leftHead rightHead)).trans
        (congrArg (qnfAdd rightHead leftHead :: ·) (rpeAddComm leftTail rightTail))

/-- **`rpxAdd` is associative** at the plain list level — each coefficient sum associates (`qnfAddAssoc`),
the empty-summand arms carry through definitionally. -/
theorem rpeAddAssoc : ∀ firstPoly middlePoly lastPoly : List QnfRat,
    rpxAdd (rpxAdd firstPoly middlePoly) lastPoly = rpxAdd firstPoly (rpxAdd middlePoly lastPoly)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | a :: as, b :: bs, c :: cs =>
      (congrArg (· :: rpxAdd (rpxAdd as bs) cs) (qnfAddAssoc a b c)).trans
        (congrArg (qnfAdd a (qnfAdd b c) :: ·) (rpeAddAssoc as bs cs))

/-- **The four-summand interchange** `(A + B) + (C + D) = (A + C) + (B + D)` for `rpxAdd` — from
associativity and commutativity, the list-level mirror of `qnfAddInterchange`. -/
theorem rpeAddInterchange (polyA polyB polyC polyD : List QnfRat) :
    rpxAdd (rpxAdd polyA polyB) (rpxAdd polyC polyD)
      = rpxAdd (rpxAdd polyA polyC) (rpxAdd polyB polyD) :=
  (rpeAddAssoc polyA polyB (rpxAdd polyC polyD)).trans
    ((congrArg (rpxAdd polyA) (rpeAddAssoc polyB polyC polyD).symm).trans
      ((congrArg (fun middle => rpxAdd polyA (rpxAdd middle polyD)) (rpeAddComm polyB polyC)).trans
        ((congrArg (rpxAdd polyA) (rpeAddAssoc polyC polyB polyD)).trans
          (rpeAddAssoc polyA polyC (rpxAdd polyB polyD)).symm)))

/-- **The shift distributes over a sum.**  `(qnfZero :: X) + (qnfZero :: Y) = qnfZero :: (X + Y)` — the
head sum is `qnfAdd qnfZero qnfZero = qnfZero`. -/
theorem rpeConsZeroAdd (leftPoly rightPoly : List QnfRat) :
    rpxAdd (qnfZero :: leftPoly) (qnfZero :: rightPoly) = qnfZero :: rpxAdd leftPoly rightPoly :=
  congrArg (· :: rpxAdd leftPoly rightPoly) (qnfAddZeroLeft qnfZero)

/-! ## T1b — the `rpxScale` layer (plain `Eq`) -/

/-- **Scaling distributes over a polynomial sum.**  `scalar · (p + q) = scalar·p + scalar·q`
(`qnfMulLeftDistrib` coefficientwise). -/
theorem rpeScaleDistributesOverAdd (scalar : QnfRat) :
    ∀ leftPoly rightPoly : List QnfRat,
      rpxScale scalar (rpxAdd leftPoly rightPoly)
        = rpxAdd (rpxScale scalar leftPoly) (rpxScale scalar rightPoly)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs =>
      (congrArg (· :: rpxScale scalar (rpxAdd as bs)) (qnfMulLeftDistrib scalar a b)).trans
        (congrArg (qnfAdd (qnfMul scalar a) (qnfMul scalar b) :: ·)
          (rpeScaleDistributesOverAdd scalar as bs))

/-- **Scaling composes.**  `(a · b) · p = a · (b · p)` (`qnfMulAssoc` coefficientwise). -/
theorem rpeScaleScaleAssoc (firstScalar secondScalar : QnfRat) :
    ∀ coeffs : List QnfRat,
      rpxScale (qnfMul firstScalar secondScalar) coeffs
        = rpxScale firstScalar (rpxScale secondScalar coeffs)
  | [] => rfl
  | c :: cs =>
      (congrArg (· :: rpxScale (qnfMul firstScalar secondScalar) cs)
          (qnfMulAssoc firstScalar secondScalar c)).trans
        (congrArg (qnfMul firstScalar (qnfMul secondScalar c) :: ·)
          (rpeScaleScaleAssoc firstScalar secondScalar cs))

/-- **A scalar sum distributes over scaling.**  `(a + b) · p = a·p + b·p` (`qnfMulRightDistrib`
coefficientwise). -/
theorem rpeScaleAddScalar (firstScalar secondScalar : QnfRat) :
    ∀ coeffs : List QnfRat,
      rpxScale (qnfAdd firstScalar secondScalar) coeffs
        = rpxAdd (rpxScale firstScalar coeffs) (rpxScale secondScalar coeffs)
  | [] => rfl
  | c :: cs =>
      (congrArg (· :: rpxScale (qnfAdd firstScalar secondScalar) cs)
          (qnfMulRightDistrib firstScalar secondScalar c)).trans
        (congrArg (qnfAdd (qnfMul firstScalar c) (qnfMul secondScalar c) :: ·)
          (rpeScaleAddScalar firstScalar secondScalar cs))

/-- **Scaling commutes past multiplication on the left.**  `(scalar · middle) × right = scalar · (middle ×
right)` (plain `Eq`) — induction on `middle`, folding `rpeScaleDistributesOverAdd` and `rpeScaleScaleAssoc`
through the `rpxMul` convolution step. -/
theorem rpeScaleMulCommLeft (scalar : QnfRat) :
    ∀ (middlePoly rightPoly : List QnfRat),
      rpxMul (rpxScale scalar middlePoly) rightPoly
        = rpxScale scalar (rpxMul middlePoly rightPoly)
  | [], _ => rfl
  | b :: bs, rightPoly => by
      show rpxAdd (rpxScale (qnfMul scalar b) rightPoly) (qnfZero :: rpxMul (rpxScale scalar bs) rightPoly)
         = rpxScale scalar (rpxAdd (rpxScale b rightPoly) (qnfZero :: rpxMul bs rightPoly))
      rw [rpeScaleDistributesOverAdd, rpeScaleScaleAssoc]
      exact congrArg (rpxAdd (rpxScale scalar (rpxScale b rightPoly)))
        ((congrArg (· :: rpxMul (rpxScale scalar bs) rightPoly) (qnfMulZeroRight scalar).symm).trans
          (congrArg (qnfMul scalar qnfZero :: ·) (rpeScaleMulCommLeft scalar bs rightPoly)))

/-! ## T1c — `rpxMul` distributivity (plain `Eq`) -/

/-- **`rpxMul` distributes on the RIGHT.**  `(p + q) × multiplier = p×multiplier + q×multiplier` (plain
`Eq`) — the aggregate-reconstruction lever.  Induction on `p, q`: the empty arms carry through, the
cons/cons arm splits the leading scalar sum (`rpeScaleAddScalar`), the shifted tail (`rpeConsZeroAdd`), and
regroups by the interchange. -/
theorem rpeMulRightDistrib :
    ∀ (leftPoly rightPoly multiplier : List QnfRat),
      rpxMul (rpxAdd leftPoly rightPoly) multiplier
        = rpxAdd (rpxMul leftPoly multiplier) (rpxMul rightPoly multiplier)
  | [], _, _ => rfl
  | a :: as, [], multiplier => (rpeAddNilRight (rpxMul (a :: as) multiplier)).symm
  | a :: as, b :: bs, multiplier => by
      have ih : rpxMul (rpxAdd as bs) multiplier
          = rpxAdd (rpxMul as multiplier) (rpxMul bs multiplier) := rpeMulRightDistrib as bs multiplier
      show rpxAdd (rpxScale (qnfAdd a b) multiplier) (qnfZero :: rpxMul (rpxAdd as bs) multiplier)
         = rpxAdd (rpxAdd (rpxScale a multiplier) (qnfZero :: rpxMul as multiplier))
             (rpxAdd (rpxScale b multiplier) (qnfZero :: rpxMul bs multiplier))
      rw [rpeScaleAddScalar, ih, ← rpeConsZeroAdd, rpeAddInterchange]

/-- **`rpxMul` distributes on the LEFT.**  `multiplier × (p + q) = multiplier×p + multiplier×q` (plain
`Eq`) — induction on `multiplier`, using `rpeScaleDistributesOverAdd`, `rpeConsZeroAdd`, the interchange. -/
theorem rpeMulLeftDistrib :
    ∀ (multiplier leftPoly rightPoly : List QnfRat),
      rpxMul multiplier (rpxAdd leftPoly rightPoly)
        = rpxAdd (rpxMul multiplier leftPoly) (rpxMul multiplier rightPoly)
  | [], _, _ => rfl
  | a :: as, leftPoly, rightPoly => by
      have ih : rpxMul as (rpxAdd leftPoly rightPoly)
          = rpxAdd (rpxMul as leftPoly) (rpxMul as rightPoly) := rpeMulLeftDistrib as leftPoly rightPoly
      show rpxAdd (rpxScale a (rpxAdd leftPoly rightPoly)) (qnfZero :: rpxMul as (rpxAdd leftPoly rightPoly))
         = rpxAdd (rpxAdd (rpxScale a leftPoly) (qnfZero :: rpxMul as leftPoly))
             (rpxAdd (rpxScale a rightPoly) (qnfZero :: rpxMul as rightPoly))
      rw [rpeScaleDistributesOverAdd, ih, ← rpeConsZeroAdd, rpeAddInterchange]

/-! ## T1d — trim congruences (via the coefficient bridge) -/

/-- **`rpxAdd` respects trim in both arguments.**  Trim-equal summands give a trim-equal sum. -/
theorem rpeAddRespectsTrim {leftA leftB rightA rightB : List QnfRat}
    (leftTrimEq : rpxTrim leftA = rpxTrim leftB)
    (rightTrimEq : rpxTrim rightA = rpxTrim rightB) :
    rpxTrim (rpxAdd leftA rightA) = rpxTrim (rpxAdd leftB rightB) := by
  apply rpdTrimEqOfCoeffEq
  intro position
  rw [rpxCoeffAdd, rpxCoeffAdd, rpeCoeffEqOfTrimEq leftTrimEq position,
    rpeCoeffEqOfTrimEq rightTrimEq position]

/-- **The shift respects trim.**  `rpxTrim X = rpxTrim Y → rpxTrim (qnfZero :: X) = rpxTrim (qnfZero :: Y)`.
-/
theorem rpeConsZeroRespectsTrim {leftPoly rightPoly : List QnfRat}
    (trimEq : rpxTrim leftPoly = rpxTrim rightPoly) :
    rpxTrim (qnfZero :: leftPoly) = rpxTrim (qnfZero :: rightPoly) := by
  apply rpdTrimEqOfCoeffEq
  intro position
  cases position with
  | zero => rfl
  | succ priorPosition => exact rpeCoeffEqOfTrimEq trimEq priorPosition

/-- **A shifted product's coefficients agree with the shift of the product.**  `rpxCoeff ((qnfZero :: X) ×
C) n = rpxCoeff (qnfZero :: (X × C)) n` — the extra `rpxScale qnfZero C` summand annihilates coefficientwise. -/
theorem rpeMulConsZeroLeftCoeff (innerPoly rightPoly : List QnfRat) (position : Nat) :
    rpxCoeff (rpxMul (qnfZero :: innerPoly) rightPoly) position
      = rpxCoeff (qnfZero :: rpxMul innerPoly rightPoly) position := by
  show rpxCoeff (rpxAdd (rpxScale qnfZero rightPoly) (qnfZero :: rpxMul innerPoly rightPoly)) position
     = rpxCoeff (qnfZero :: rpxMul innerPoly rightPoly) position
  rw [rpxCoeffAdd, rpxCoeffScale, qnfMulZeroLeft, qnfAddZeroLeft]

/-- Trim form of `rpeMulConsZeroLeftCoeff`. -/
theorem rpeMulConsZeroLeftTrim (innerPoly rightPoly : List QnfRat) :
    rpxTrim (rpxMul (qnfZero :: innerPoly) rightPoly)
      = rpxTrim (qnfZero :: rpxMul innerPoly rightPoly) :=
  rpdTrimEqOfCoeffEq _ _ (rpeMulConsZeroLeftCoeff innerPoly rightPoly)

/-- **`rpxMul` reads only the right factor's coefficients.**  If `rightA` and `rightB` have equal
coefficients everywhere then `leftPoly × rightA` and `leftPoly × rightB` do too — induction on `leftPoly`,
casing the position through the convolution shift. -/
theorem rpeMulCoeffCongrRight (rightA rightB : List QnfRat)
    (coeffAgree : ∀ position : Nat, rpxCoeff rightA position = rpxCoeff rightB position) :
    ∀ (leftPoly : List QnfRat) (position : Nat),
      rpxCoeff (rpxMul leftPoly rightA) position = rpxCoeff (rpxMul leftPoly rightB) position
  | [], _ => rfl
  | a :: as, position => by
      show rpxCoeff (rpxAdd (rpxScale a rightA) (qnfZero :: rpxMul as rightA)) position
         = rpxCoeff (rpxAdd (rpxScale a rightB) (qnfZero :: rpxMul as rightB)) position
      rw [rpxCoeffAdd, rpxCoeffAdd, rpxCoeffScale, rpxCoeffScale, coeffAgree position]
      cases position with
      | zero => rfl
      | succ priorPosition =>
          show qnfAdd (qnfMul a (rpxCoeff rightB (priorPosition + 1)))
                (rpxCoeff (rpxMul as rightA) priorPosition)
             = qnfAdd (qnfMul a (rpxCoeff rightB (priorPosition + 1)))
                (rpxCoeff (rpxMul as rightB) priorPosition)
          exact congrArg (qnfAdd (qnfMul a (rpxCoeff rightB (priorPosition + 1))))
            (rpeMulCoeffCongrRight rightA rightB coeffAgree as priorPosition)

/-- **`rpxMul` respects trim in the right argument.**  `rpxTrim rightA = rpxTrim rightB → rpxTrim (leftPoly
× rightA) = rpxTrim (leftPoly × rightB)`. -/
theorem rpeMulRespectsTrimRight (leftPoly rightA rightB : List QnfRat)
    (trimEq : rpxTrim rightA = rpxTrim rightB) :
    rpxTrim (rpxMul leftPoly rightA) = rpxTrim (rpxMul leftPoly rightB) :=
  rpdTrimEqOfCoeffEq (rpxMul leftPoly rightA) (rpxMul leftPoly rightB)
    (rpeMulCoeffCongrRight rightA rightB (rpeCoeffEqOfTrimEq trimEq) leftPoly)

/-- **A singleton scales.**  `rpxCoeff ([scalar] × rightPoly) n = scalar · rpxCoeff rightPoly n`. -/
theorem rpeSingletonMulCoeff (scalar : QnfRat) (rightPoly : List QnfRat) (position : Nat) :
    rpxCoeff (rpxMul [scalar] rightPoly) position = qnfMul scalar (rpxCoeff rightPoly position) := by
  show rpxCoeff (rpxAdd (rpxScale scalar rightPoly) [qnfZero]) position
     = qnfMul scalar (rpxCoeff rightPoly position)
  rw [rpxCoeffAdd, rpxCoeffScale, rpdCoeffSingletonZero, qnfAddZeroRight]

/-- **The constant `1` is a left multiplicative unit up to trim.**  `rpxTrim ([qnfOne] × poly) = rpxTrim
poly`. -/
theorem rpeMulOneLeftTrim (rightPoly : List QnfRat) :
    rpxTrim (rpxMul [qnfOne] rightPoly) = rpxTrim rightPoly :=
  rpdTrimEqOfCoeffEq (rpxMul [qnfOne] rightPoly) rightPoly (fun position =>
    (rpeSingletonMulCoeff qnfOne rightPoly position).trans (qnfMulOneLeft (rpxCoeff rightPoly position)))

/-! ## T1e — `rpxMul` associativity (trim level) -/

/-- **`rpxMul` is associative up to trim.**  `rpxTrim ((A × B) × C) = rpxTrim (A × (B × C))` — induction on
`A`: the leading term commutes scale past `rpxMul` (`rpeScaleMulCommLeft`), the shifted tail goes through
`rpeMulConsZeroLeftTrim` + `rpeConsZeroRespectsTrim` + the inductive hypothesis, and the two share the same
first summand (`rpeAddRespectsTrim`).  Only trim-equal because `rpxMul (qnfZero :: _)` and
`rpxScale qnfZero` pad with trailing zeros the plain list keeps. -/
theorem rpeMulAssocTrim : ∀ (leftA middleB rightC : List QnfRat),
    rpxTrim (rpxMul (rpxMul leftA middleB) rightC)
      = rpxTrim (rpxMul leftA (rpxMul middleB rightC))
  | [], _, _ => rfl
  | a :: as, middleB, rightC => by
      have ih : rpxTrim (rpxMul (rpxMul as middleB) rightC)
          = rpxTrim (rpxMul as (rpxMul middleB rightC)) := rpeMulAssocTrim as middleB rightC
      have distribStep :
          rpxMul (rpxMul (a :: as) middleB) rightC
            = rpxAdd (rpxScale a (rpxMul middleB rightC))
                (rpxMul (qnfZero :: rpxMul as middleB) rightC) := by
        show rpxMul (rpxAdd (rpxScale a middleB) (qnfZero :: rpxMul as middleB)) rightC
           = rpxAdd (rpxScale a (rpxMul middleB rightC))
               (rpxMul (qnfZero :: rpxMul as middleB) rightC)
        rw [rpeMulRightDistrib, rpeScaleMulCommLeft]
      rw [distribStep]
      show rpxTrim (rpxAdd (rpxScale a (rpxMul middleB rightC))
              (rpxMul (qnfZero :: rpxMul as middleB) rightC))
         = rpxTrim (rpxAdd (rpxScale a (rpxMul middleB rightC))
              (qnfZero :: rpxMul as (rpxMul middleB rightC)))
      apply rpeAddRespectsTrim rfl
      exact (rpeMulConsZeroLeftTrim (rpxMul as middleB) rightC).trans
        (rpeConsZeroRespectsTrim ih)

/-! ## T2 — the aggregate division reconstruction (trim / polynomial level) -/

/-- **THE AGGREGATE RECONSTRUCTION.**  `rpxTrim (quotient·divisor + remainder) = rpxTrim dividend` at every
fuel — the coefficient-level content the committed eval-only `rpxDivModReconstructs` does not give.  Fuel
induction on `rpxDivMod`: the guard/base leaves the dividend untouched; the reduction step splits the
accumulated quotient by RIGHT-distributivity, re-associates (`rpeAddAssoc`), and folds the reduced dividend
back through the coefficient bridge (`rpeCoeffEqOfTrimEq` on the inductive hypothesis, `rpxCoeffSub`, and the
additive cancellation `rpdQnfAddSubSelf`). -/
theorem rpeDivModReconstructsTrim :
    ∀ (fuel : Nat) (divisor dividend : List QnfRat),
      rpxTrim (rpxAdd (rpxMul (rpxDivMod fuel divisor dividend).1 divisor)
          (rpxDivMod fuel divisor dividend).2)
        = rpxTrim dividend
  | 0, divisor, dividend => rfl
  | fuel + 1, divisor, dividend => by
      dsimp only [rpxDivMod]
      cases Nat.decLt (rpxDegree dividend) (rpxDegree divisor) with
      | isTrue _ => rfl
      | isFalse _ =>
          rw [rpeMulRightDistrib, rpeAddAssoc]
          apply rpdTrimEqOfCoeffEq
          intro position
          rw [rpxCoeffAdd,
            rpeCoeffEqOfTrimEq (rpeDivModReconstructsTrim fuel divisor
              (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))) position,
            rpxCoeffSub]
          exact rpdQnfAddSubSelf
            (rpxCoeff (rpxMul (rpxQuotientTerm divisor dividend) divisor) position)
            (rpxCoeff dividend position)

/-! ## T3 — divisibility and "gcd divides both" -/

/-- **Trim-level divisibility.**  `rpeDivides divisor dividend` iff some `cofactor` has `rpxTrim (cofactor ×
divisor) = rpxTrim dividend` — divisor divides dividend as polynomials up to the trailing-zero normal form. -/
def rpeDivides (divisor dividend : List QnfRat) : Prop :=
  ∃ cofactor : List QnfRat, rpxTrim (rpxMul cofactor divisor) = rpxTrim dividend

/-- **Everything divides the zero polynomial.**  If `dividend` trims to `[]`, the empty cofactor witnesses
`rpeDivides divisor dividend`. -/
theorem rpeDividesOfDividendTrimNil (divisor dividend : List QnfRat)
    (dividendTrimNil : rpxTrim dividend = []) : rpeDivides divisor dividend :=
  ⟨[], dividendTrimNil.symm⟩

/-- **Reflexivity.**  `rpeDivides poly poly` with the constant-`1` cofactor. -/
theorem rpeDividesRefl (poly : List QnfRat) : rpeDivides poly poly :=
  ⟨[qnfOne], rpeMulOneLeftTrim poly⟩

/-- **Divisibility respects trim in the dividend.**  Trim-equal dividends have the same divisors. -/
theorem rpeDividesRespectsTrim (divisor dividendA dividendB : List QnfRat)
    (trimEq : rpxTrim dividendA = rpxTrim dividendB)
    (divides : rpeDivides divisor dividendA) : rpeDivides divisor dividendB := by
  obtain ⟨cofactor, cofactorEq⟩ := divides
  exact ⟨cofactor, cofactorEq.trans trimEq⟩

/-- **Adding a zero-trim tail leaves the trim unchanged.**  `rpxTrim rightPoly = [] → rpxTrim (leftPoly +
rightPoly) = rpxTrim leftPoly`. -/
theorem rpeTrimAddRightTrimNil (leftPoly rightPoly : List QnfRat)
    (rightTrimNil : rpxTrim rightPoly = []) :
    rpxTrim (rpxAdd leftPoly rightPoly) = rpxTrim leftPoly :=
  rpdTrimEqOfCoeffEq (rpxAdd leftPoly rightPoly) leftPoly (fun position => by
    rw [rpxCoeffAdd, rpdCoeffZeroOfTrimNil rightPoly position rightTrimNil, qnfAddZeroRight])

/-- **Zero remainder means the divisor divides the dividend.**  From the aggregate reconstruction (T2),
when the remainder trims to `[]` the quotient witnesses `rpeDivides divisor dividend`. -/
theorem rpeExactDivisionGivesDivides (fuel : Nat) (divisor dividend : List QnfRat)
    (remainderTrimNil : rpxTrim (rpxDivMod fuel divisor dividend).2 = []) :
    rpeDivides divisor dividend :=
  ⟨(rpxDivMod fuel divisor dividend).1,
    (rpeTrimAddRightTrimNil (rpxMul (rpxDivMod fuel divisor dividend).1 divisor)
        (rpxDivMod fuel divisor dividend).2 remainderTrimNil).symm.trans
      (rpeDivModReconstructsTrim fuel divisor dividend)⟩

/-- **A common divisor divides any left-cofactor combination.**  `divisor | first → divisor | second →
divisor | (cofactor×first + second)` — substitute both witnesses, associate the cofactor through
`rpeMulAssocTrim`, transport the substituted factor with `rpeMulRespectsTrimRight`, and recombine by
RIGHT-distributivity.  The Euclidean step's algebraic heart. -/
theorem rpeLinearCombinationDivides (divisor firstPoly secondPoly cofactorPoly : List QnfRat)
    (dividesFirst : rpeDivides divisor firstPoly)
    (dividesSecond : rpeDivides divisor secondPoly) :
    rpeDivides divisor (rpxAdd (rpxMul cofactorPoly firstPoly) secondPoly) := by
  obtain ⟨firstWitness, firstEq⟩ := dividesFirst
  obtain ⟨secondWitness, secondEq⟩ := dividesSecond
  refine ⟨rpxAdd (rpxMul cofactorPoly firstWitness) secondWitness, ?_⟩
  rw [rpeMulRightDistrib]
  apply rpeAddRespectsTrim
  · exact (rpeMulAssocTrim cofactorPoly firstWitness divisor).trans
      (rpeMulRespectsTrimRight cofactorPoly (rpxMul firstWitness divisor) firstPoly firstEq)
  · exact secondEq

/-- **The Euclidean "gcd divides both" invariant, with the honest fuel-adequacy bound.**  With a fixed
`bound` dominating both trimmed lengths and `(rpxTrim secondary).length + bound < fuel`, the final
`rpxGcd fuel primary secondary` divides both `primary` and `secondary`.  Fuel induction: the terminal case
(`secondary` trims to `[]`) returns `primary`, which divides itself and the zero `secondary`; the reduction
step recurses on `(secondary, remainder)` — the remainder's degree bound (`rpdRemainderAdequate`) keeps the
measure `(rpxTrim secondary).length + bound` strictly below `fuel`, and "gcd divides both of the reduced
pair" transports back to `primary` via the aggregate reconstruction (T2) and the linear-combination lemma. -/
theorem rpeGcdDividesBothInvariant (bound : Nat) :
    ∀ (fuel : Nat) (primary secondary : List QnfRat),
      (rpxTrim primary).length ≤ bound →
      (rpxTrim secondary).length ≤ bound →
      (rpxTrim secondary).length + bound < fuel →
      rpeDivides (rpxGcd fuel primary secondary) primary
        ∧ rpeDivides (rpxGcd fuel primary secondary) secondary
  | 0, _primary, _secondary, _, _, fuelBound => absurd fuelBound (Nat.not_lt_zero _)
  | fuel + 1, primary, secondary, primaryBound, secondaryBound, fuelBound => by
      dsimp only [rpxGcd]
      cases hSecondaryTrim : rpxTrim secondary with
      | nil =>
          exact ⟨rpeDividesRefl primary,
            rpeDividesOfDividendTrimNil primary secondary hSecondaryTrim⟩
      | cons trimHead trimTail =>
          have secondaryNonzero : rpxTrim secondary ≠ [] := by
            rw [hSecondaryTrim]; exact List.cons_ne_nil trimHead trimTail
          have secondaryLenEq : (rpxTrim secondary).length = rpxDegree secondary + 1 :=
            rpxTrimLengthEqDegreeSucc secondary secondaryNonzero
          have primaryFitsFuel : (rpxTrim primary).length ≤ fuel :=
            Nat.le_trans primaryBound
              (Nat.le_trans (Nat.le_add_left bound (rpxTrim secondary).length)
                (Nat.le_of_lt_succ fuelBound))
          have remAdequate : rpxTrim (rpxRemainder fuel secondary primary) = []
              ∨ rpxDegree (rpxRemainder fuel secondary primary) < rpxDegree secondary :=
            rpdRemainderAdequate fuel secondary primary secondaryNonzero primaryFitsFuel
          have degSecLeBound : rpxDegree secondary ≤ bound := by
            have hh : rpxDegree secondary + 1 ≤ bound := by rw [← secondaryLenEq]; exact secondaryBound
            exact Nat.le_trans (Nat.le_succ (rpxDegree secondary)) hh
          have remTrimLenLe : (rpxTrim (rpxRemainder fuel secondary primary)).length ≤ rpxDegree secondary := by
            cases hRem : rpxTrim (rpxRemainder fuel secondary primary) with
            | nil => exact Nat.zero_le (rpxDegree secondary)
            | cons remHead remTail =>
                have remNonzero : rpxTrim (rpxRemainder fuel secondary primary) ≠ [] := by
                  rw [hRem]; exact List.cons_ne_nil remHead remTail
                have degLt : rpxDegree (rpxRemainder fuel secondary primary) < rpxDegree secondary :=
                  remAdequate.resolve_left remNonzero
                have remLenEq : (remHead :: remTail).length
                    = rpxDegree (rpxRemainder fuel secondary primary) + 1 := by
                  rw [← hRem]
                  exact rpxTrimLengthEqDegreeSucc (rpxRemainder fuel secondary primary) remNonzero
                rw [remLenEq]; exact degLt
          have remBoundLe : (rpxTrim (rpxRemainder fuel secondary primary)).length ≤ bound :=
            Nat.le_trans remTrimLenLe degSecLeBound
          have remFuelBound : (rpxTrim (rpxRemainder fuel secondary primary)).length + bound < fuel := by
            have step_a : (rpxTrim (rpxRemainder fuel secondary primary)).length + bound
                ≤ rpxDegree secondary + bound := Nat.add_le_add_right remTrimLenLe bound
            have step_b : rpxDegree secondary + bound < (rpxTrim secondary).length + bound := by
              rw [secondaryLenEq]
              exact Nat.add_lt_add_right (Nat.lt_succ_self (rpxDegree secondary)) bound
            have step_c : (rpxTrim secondary).length + bound ≤ fuel := Nat.le_of_lt_succ fuelBound
            exact Nat.lt_of_le_of_lt step_a (Nat.lt_of_lt_of_le step_b step_c)
          have ih := rpeGcdDividesBothInvariant bound fuel secondary
            (rpxRemainder fuel secondary primary) secondaryBound remBoundLe remFuelBound
          refine ⟨?_, ih.1⟩
          have reconPrimary : rpxTrim (rpxAdd (rpxMul (rpxDivMod fuel secondary primary).1 secondary)
              (rpxRemainder fuel secondary primary)) = rpxTrim primary :=
            rpeDivModReconstructsTrim fuel secondary primary
          have combo : rpeDivides (rpxGcd fuel secondary (rpxRemainder fuel secondary primary))
              (rpxAdd (rpxMul (rpxDivMod fuel secondary primary).1 secondary)
                (rpxRemainder fuel secondary primary)) :=
            rpeLinearCombinationDivides (rpxGcd fuel secondary (rpxRemainder fuel secondary primary))
              secondary (rpxRemainder fuel secondary primary) (rpxDivMod fuel secondary primary).1
              ih.1 ih.2
          exact rpeDividesRespectsTrim _ _ _ reconPrimary combo

/-- **THE THEOREM — `rpxGcd` divides both inputs** at the adequate fuel `|primary| + |secondary| +
(|primary| + |secondary|) + 1`.  Supersedes the committed owner-false `rpxHasGcdDividesBoth` /
`rpdHasGcdDividesBoth`. -/
theorem rpeGcdDividesBoth (primary secondary : List QnfRat) :
    rpeDivides (rpxGcd (primary.length + secondary.length
        + (primary.length + secondary.length) + 1) primary secondary) primary
      ∧ rpeDivides (rpxGcd (primary.length + secondary.length
        + (primary.length + secondary.length) + 1) primary secondary) secondary := by
  have secondaryTrimLe : (rpxTrim secondary).length ≤ primary.length + secondary.length :=
    Nat.le_trans (rpdTrimLengthLe secondary) (Nat.le_add_left secondary.length primary.length)
  exact rpeGcdDividesBothInvariant (primary.length + secondary.length)
    (primary.length + secondary.length + (primary.length + secondary.length) + 1)
    primary secondary
    (Nat.le_trans (rpdTrimLengthLe primary) (Nat.le_add_right primary.length secondary.length))
    secondaryTrimLe
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right secondaryTrimLe (primary.length + secondary.length))
      (Nat.lt_succ_self (primary.length + secondary.length + (primary.length + secondary.length))))

/-- **`rpxGcd` divides the first input** (left projection of `rpeGcdDividesBoth`). -/
theorem rpeGcdDividesLeft (primary secondary : List QnfRat) :
    rpeDivides (rpxGcd (primary.length + secondary.length
        + (primary.length + secondary.length) + 1) primary secondary) primary :=
  (rpeGcdDividesBoth primary secondary).1

/-- **`rpxGcd` divides the second input** (right projection of `rpeGcdDividesBoth`). -/
theorem rpeGcdDividesRight (primary secondary : List QnfRat) :
    rpeDivides (rpxGcd (primary.length + secondary.length
        + (primary.length + secondary.length) + 1) primary secondary) secondary :=
  (rpeGcdDividesBoth primary secondary).2

/-! ## Groundings (fires)

Closed-value kernel pins; the ring pipeline reduces to canonical `QnfRat` normal forms, so the plain-`Eq`
ring laws hold by `rfl` at small instances, and the gcd-divides facts hold by exact-division `rfl` pins and
by the general theorems. -/

set_option maxRecDepth 8192

/-- Fire: `rpxAdd` commutes at `(1 + 2x) + 3`. -/
theorem rpeFireAddCommClosed :
    rpxAdd [qnfOfInt 1, qnfOfInt 2] [qnfOfInt 3] = rpxAdd [qnfOfInt 3] [qnfOfInt 1, qnfOfInt 2] := rfl

/-- Fire: `rpxAdd` associates at `((1) + (2)) + (3)`. -/
theorem rpeFireAddAssocClosed :
    rpxAdd (rpxAdd [qnfOfInt 1] [qnfOfInt 2]) [qnfOfInt 3]
      = rpxAdd [qnfOfInt 1] (rpxAdd [qnfOfInt 2] [qnfOfInt 3]) := rfl

/-- Fire: RIGHT-distributivity at `((1) + (2)) · (1 + x)`. -/
theorem rpeFireRightDistribClosed :
    rpxMul (rpxAdd [qnfOfInt 1] [qnfOfInt 2]) [qnfOfInt 1, qnfOfInt 1]
      = rpxAdd (rpxMul [qnfOfInt 1] [qnfOfInt 1, qnfOfInt 1])
          (rpxMul [qnfOfInt 2] [qnfOfInt 1, qnfOfInt 1]) := rfl

/-- Fire: LEFT-distributivity at `(1 + x) · ((1) + (2))`. -/
theorem rpeFireLeftDistribClosed :
    rpxMul [qnfOfInt 1, qnfOfInt 1] (rpxAdd [qnfOfInt 1] [qnfOfInt 2])
      = rpxAdd (rpxMul [qnfOfInt 1, qnfOfInt 1] [qnfOfInt 1])
          (rpxMul [qnfOfInt 1, qnfOfInt 1] [qnfOfInt 2]) := rfl

/-- Fire: scaling distributes over a sum at `2 · ((1 + x) + (3))`. -/
theorem rpeFireScaleDistribClosed :
    rpxScale (qnfOfInt 2) (rpxAdd [qnfOfInt 1, qnfOfInt 1] [qnfOfInt 3])
      = rpxAdd (rpxScale (qnfOfInt 2) [qnfOfInt 1, qnfOfInt 1]) (rpxScale (qnfOfInt 2) [qnfOfInt 3]) := rfl

/-- Fire: `rpxMul` associates up to trim at `((1 + x) · (2)) · (3 + x)`. -/
theorem rpeFireMulAssocTrimClosed :
    rpxTrim (rpxMul (rpxMul [qnfOfInt 1, qnfOfInt 1] [qnfOfInt 2]) [qnfOfInt 3, qnfOfInt 1])
      = rpxTrim (rpxMul [qnfOfInt 1, qnfOfInt 1] (rpxMul [qnfOfInt 2] [qnfOfInt 3, qnfOfInt 1])) := rfl

/-- Fire (aggregate reconstruction, closed value): `x² − 1 = (x−1)(x+1) + 0` reconstructs at the trimmed
level — `quotient·(x−1) + remainder` trims back to `x² − 1`. -/
theorem rpeFireReconstructsTrimClosed :
    rpxTrim (rpxAdd (rpxMul (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1]
          [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).1 [qnfOfInt (-1), qnfOfInt 1])
        (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).2)
      = rpxTrim [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] :=
  rpeDivModReconstructsTrim 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]

/-- Fire (exact division ⟹ divides): `x − 1` divides `x² − 1` — zero remainder witnesses the quotient. -/
theorem rpeFireExactDividesDifferenceOfSquares :
    rpeDivides [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] :=
  rpeExactDivisionGivesDivides 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] rfl

/-- Fire (gcd divides both, computational): the gcd of `x² − 1` and `x − 1` divides `x² − 1` exactly — the
computed gcd (`= x − 1`) leaves zero remainder dividing `x² − 1`. -/
theorem rpeFireGcdDividesDifferenceOfSquaresComputed :
    rpxTrim (rpxDivMod 3 (rpxGcd 5 [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1])
        [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).2 = [] := rfl

/-- Fire (gcd divides both, computational): the same gcd divides `x − 1` exactly. -/
theorem rpeFireGcdDividesLinearComputed :
    rpxTrim (rpxDivMod 2 (rpxGcd 5 [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1])
        [qnfOfInt (-1), qnfOfInt 1]).2 = [] := rfl

/-- Fire (the general theorem, instantiated): `rpxGcd` at the adequate fuel divides `x² − 1`. -/
theorem rpeFireGcdDividesLeftDifferenceOfSquares :
    rpeDivides (rpxGcd ([qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1].length + [qnfOfInt (-1), qnfOfInt 1].length
        + ([qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1].length + [qnfOfInt (-1), qnfOfInt 1].length) + 1)
      [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1])
      [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] :=
  rpeGcdDividesLeft [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]

/-- Fire (the general theorem, instantiated): `rpxGcd` at the adequate fuel divides `x − 1`. -/
theorem rpeFireGcdDividesRightDifferenceOfSquares :
    rpeDivides (rpxGcd ([qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1].length + [qnfOfInt (-1), qnfOfInt 1].length
        + ([qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1].length + [qnfOfInt (-1), qnfOfInt 1].length) + 1)
      [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1])
      [qnfOfInt (-1), qnfOfInt 1] :=
  rpeGcdDividesRight [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]

/-! ## Content marker -/

/-- "gcd divides both" over ℚ[x] is decided. The coefficient lists carry a commutative-ring layer
(`rpxAdd` comm/assoc/interchange, `rpxScale` distributivity/composition, `rpxMul` two-sided distributivity at
plain `Eq`, and trim-level `rpxMul` associativity `rpeMulAssocTrim`). The aggregate division reconstruction
`rpeDivModReconstructsTrim` reconstructs the dividend as a polynomial at every fuel. From these,
`rpeGcdDividesBoth` shows `rpxGcd` divides both inputs at the adequate fuel, via trim-level divisibility
(`rpeDivides`), zero-remainder divisibility (`rpeExactDivisionGivesDivides`), the linear-combination lemma
(`rpeLinearCombinationDivides`), and the fuel-adequate Euclidean invariant (`rpeGcdDividesBothInvariant`). The
full Bezout identity is decided downstream (`rbzHasBezoutIdentity`). -/
def rpeHasGcdDividesBoth : Bool := true

end FX1Poly.ComputerAlgebra
