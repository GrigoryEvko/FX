import FX1Poly.ComputerAlgebra.Number.NormalizedRational

/-! # RationalPolynomial — the ℚ[x] substrate with Euclidean division

The committed ℤ[x] kit reaches the invariant-factor GCD only through pseudo-division (over ℤ one cannot divide
by a leading coefficient other than `±1`). Over the field ℚ every nonzero leading coefficient is invertible via
`qnfInv`, so the quotient term is `leadDividend · leadDivisor⁻¹ · x^Δ` and division produces a true remainder —
the named prerequisite for invariant factors over ℚ[x] / rational canonical form.

A univariate rational polynomial is its ascending coefficient list over `QnfRat` (`[c₀, …, cₙ]` denotes
`c₀ + c₁·x + ⋯ + cₙ·xⁿ`); trailing zeros are permitted, `rpxTrim` is the canonical trailing-zero-free form, and
`rpxIsCanonical` records "the last surviving coefficient is nonzero". Evaluation `rpxEval point` is a ring
homomorphism `ℚ[x] → ℚ` (`rpxEvalAdd`/`rpxEvalScale`/`rpxEvalMul`/`rpxEvalNeg`/`rpxEvalSub`), and `rpxTrim`
preserves evaluation. `rpxDivModReconstructs` is the division invariant
`eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder)` at every fuel, resting only on the ring
homomorphism, hence independent of whether the fuel sufficed. `rpxDividesEvalMultiple` drops the remainder once
it trims to zero. The Euclidean GCD `rpxGcd` captures every common root of its inputs
(`rpxGcdVanishesAtCommonRoot`), with the shared-linear-factor bridge.

The remainder degree bound and "gcd divides both" both require fuel adequacy, supplied downstream — the degree
bound in `RationalPolynomialDegree` (`rpdHasRemainderDegreeBound`), "gcd divides both" and Bezout in
`RationalPolynomialRing`/`RationalPolynomialBezout` (`rpeHasGcdDividesBoth`, `rbzHasBezoutIdentity`).

All coefficient arithmetic routes through the shipped `qnf*` field laws; every definition is structural on the
list or on `fuel`; the only non-list case analyses are `qnfDecEq _ qnfZero` and `Nat.decLt` (full enumeration).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, or `WellFounded.fix`.
Per-declaration audit twin in the matching `FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Derived `QnfRat` ring helpers (zero absorption and negation, from the shipped field laws) -/

/-- `(a + b) + (c + d) = (a + c) + (b + d)` over ℚ — associativity and commutativity of addition. -/
theorem qnfAddInterchange (valueA valueB valueC valueD : QnfRat) :
    qnfAdd (qnfAdd valueA valueB) (qnfAdd valueC valueD)
      = qnfAdd (qnfAdd valueA valueC) (qnfAdd valueB valueD) :=
  (qnfAddAssoc valueA valueB (qnfAdd valueC valueD)).trans
    ((congrArg (qnfAdd valueA) (qnfAddAssoc valueB valueC valueD).symm).trans
      ((congrArg (fun middle => qnfAdd valueA (qnfAdd middle valueD)) (qnfAddComm valueB valueC)).trans
        ((congrArg (qnfAdd valueA) (qnfAddAssoc valueC valueB valueD)).trans
          (qnfAddAssoc valueA valueC (qnfAdd valueB valueD)).symm)))

/-- **Zero absorbs on the left.**  `0 · value = 0` — from `0 = 0 + 0` and right distributivity `value` is
its own double, and a self-double cancels to zero. -/
theorem qnfMulZeroLeft (value : QnfRat) : qnfMul qnfZero value = qnfZero :=
  have productSelfSum :
      qnfMul qnfZero value = qnfAdd (qnfMul qnfZero value) (qnfMul qnfZero value) :=
    (congrArg (qnfMul · value) (qnfAddZeroLeft qnfZero)).symm.trans
      (qnfMulRightDistrib qnfZero qnfZero value)
  (((qnfAddNegLeft (qnfMul qnfZero value)).symm.trans
      (congrArg (qnfAdd (qnfNeg (qnfMul qnfZero value))) productSelfSum)).trans
    ((qnfAddAssoc (qnfNeg (qnfMul qnfZero value)) (qnfMul qnfZero value)
          (qnfMul qnfZero value)).symm.trans
      ((congrArg (qnfAdd · (qnfMul qnfZero value)) (qnfAddNegLeft (qnfMul qnfZero value))).trans
        (qnfAddZeroLeft (qnfMul qnfZero value))))).symm

/-- **Zero absorbs on the right.**  `value · 0 = 0` — commute and reuse the left absorber. -/
theorem qnfMulZeroRight (value : QnfRat) : qnfMul value qnfZero = qnfZero :=
  (qnfMulComm value qnfZero).trans (qnfMulZeroLeft value)

/-- **Negation of zero is zero.** -/
theorem qnfNegZero : qnfNeg qnfZero = qnfZero :=
  (qnfAddZeroLeft (qnfNeg qnfZero)).symm.trans (qnfAddNegRight qnfZero)

/-- **Negation distributes over addition.**  `-(a + b) = (-a) + (-b)` — the sum of the two negations is
the additive inverse of `a + b` (via the interchange), and inverses are unique. -/
theorem qnfNegAdd (leftValue rightValue : QnfRat) :
    qnfNeg (qnfAdd leftValue rightValue) = qnfAdd (qnfNeg leftValue) (qnfNeg rightValue) :=
  have sumZero :
      qnfAdd (qnfAdd leftValue rightValue) (qnfAdd (qnfNeg leftValue) (qnfNeg rightValue))
        = qnfZero :=
    (qnfAddInterchange leftValue rightValue (qnfNeg leftValue) (qnfNeg rightValue)).trans
      (((congrArg (qnfAdd · (qnfAdd rightValue (qnfNeg rightValue))) (qnfAddNegRight leftValue)).trans
          (congrArg (qnfAdd qnfZero) (qnfAddNegRight rightValue))).trans
        (qnfAddZeroLeft qnfZero))
  ((qnfAddZeroRight (qnfNeg (qnfAdd leftValue rightValue))).symm.trans
    (congrArg (qnfAdd (qnfNeg (qnfAdd leftValue rightValue))) sumZero.symm)).trans
    ((qnfAddAssoc (qnfNeg (qnfAdd leftValue rightValue)) (qnfAdd leftValue rightValue)
        (qnfAdd (qnfNeg leftValue) (qnfNeg rightValue))).symm.trans
      ((congrArg (qnfAdd · (qnfAdd (qnfNeg leftValue) (qnfNeg rightValue)))
          (qnfAddNegLeft (qnfAdd leftValue rightValue))).trans
        (qnfAddZeroLeft (qnfAdd (qnfNeg leftValue) (qnfNeg rightValue)))))

/-- **Multiplication pushes past negation on the right.**  `a · (-b) = -(a · b)` — `a·(-b) + a·b =
a·((-b)+b) = a·0 = 0`, and the additive inverse is unique. -/
theorem qnfMulNegRight (leftFactor rightFactor : QnfRat) :
    qnfMul leftFactor (qnfNeg rightFactor) = qnfNeg (qnfMul leftFactor rightFactor) :=
  have sumZero :
      qnfAdd (qnfMul leftFactor (qnfNeg rightFactor)) (qnfMul leftFactor rightFactor) = qnfZero :=
    (qnfMulLeftDistrib leftFactor (qnfNeg rightFactor) rightFactor).symm.trans
      ((congrArg (qnfMul leftFactor) (qnfAddNegLeft rightFactor)).trans (qnfMulZeroRight leftFactor))
  ((qnfAddZeroRight (qnfMul leftFactor (qnfNeg rightFactor))).symm.trans
    (congrArg (qnfAdd (qnfMul leftFactor (qnfNeg rightFactor)))
      (qnfAddNegRight (qnfMul leftFactor rightFactor)).symm)).trans
    ((qnfAddAssoc (qnfMul leftFactor (qnfNeg rightFactor)) (qnfMul leftFactor rightFactor)
        (qnfNeg (qnfMul leftFactor rightFactor))).symm.trans
      ((congrArg (qnfAdd · (qnfNeg (qnfMul leftFactor rightFactor))) sumZero).trans
        (qnfAddZeroLeft (qnfNeg (qnfMul leftFactor rightFactor)))))

/-- **A subtraction re-adds to its minuend.**  `(minuend − subtrahend) + subtrahend = minuend`. -/
theorem qnfAddSubCancel (minuend subtrahend : QnfRat) :
    qnfAdd (qnfSub minuend subtrahend) subtrahend = minuend :=
  (congrArg (qnfAdd · subtrahend) (qnfSubEqAddNeg minuend subtrahend)).trans
    ((qnfAddAssoc minuend (qnfNeg subtrahend) subtrahend).trans
      ((congrArg (qnfAdd minuend) (qnfAddNegLeft subtrahend)).trans
        (qnfAddZeroRight minuend)))

/-- A nonzero rational compares `false` against `qnfZero` — the contrapositive of `qnfBeqIffEq`. -/
theorem qnfBeqFalseOfNe {value : QnfRat} (isDistinct : value ≠ qnfZero) :
    qnfBeq value qnfZero = false :=
  match hBeq : qnfBeq value qnfZero with
  | true => absurd ((qnfBeqIffEq value qnfZero).mp hBeq) isDistinct
  | false => rfl

/-! ## The trailing-zero normal form, degree, and leading coefficient (T1) -/

/-- Drop trailing zeros from the ascending coefficient list, giving the canonical representative.
Structural on the list; the recursive call trims the tail first, and an empty trimmed tail defers to
whether this coefficient is zero (`qnfDecEq _ qnfZero`, full `isTrue`/`isFalse` enumeration). -/
def rpxTrim : List QnfRat → List QnfRat
  | [] => []
  | coeff :: restCoeffs =>
      match rpxTrim restCoeffs with
      | [] =>
          match qnfDecEq coeff qnfZero with
          | isTrue _ => []
          | isFalse _ => [coeff]
      | trimHead :: trimTail => coeff :: trimHead :: trimTail

/-- The last coefficient of a list, or `qnfZero` for the empty list — the leading coefficient once applied
to a trimmed polynomial. -/
def rpxLastOrZero : List QnfRat → QnfRat
  | [] => qnfZero
  | coeff :: [] => coeff
  | _ :: (nextCoeff :: rest) => rpxLastOrZero (nextCoeff :: rest)

/-- Degree of the polynomial: one less than the trimmed length (the zero polynomial gets `0`). -/
def rpxDegree (coeffs : List QnfRat) : Nat :=
  (rpxTrim coeffs).length - 1

/-- Leading coefficient: the last surviving coefficient after trimming (`qnfZero` for the zero
polynomial). -/
def rpxLeadingCoeff (coeffs : List QnfRat) : QnfRat :=
  rpxLastOrZero (rpxTrim coeffs)

/-- **Canonicality**: the empty list is canonical; a nonempty list is canonical exactly when its last
surviving coefficient is nonzero (`qnfBeq _ qnfZero = false`), i.e. it carries no trailing zero. -/
def rpxIsCanonical : List QnfRat → Bool
  | [] => true
  | coeff :: restCoeffs => not (qnfBeq (rpxLastOrZero (coeff :: restCoeffs)) qnfZero)

/-- **Trimming produces a canonical polynomial.**  `rpxIsCanonical (rpxTrim coeffs) = true`: the trimmed
form never ends in a zero.  Induction on the list, casing on the trimmed tail (and, when empty, on whether
the head is zero — a nonzero surviving head is exactly canonical). -/
theorem rpxTrimIsCanonical : ∀ coeffs : List QnfRat, rpxIsCanonical (rpxTrim coeffs) = true
  | [] => rfl
  | coeff :: restCoeffs => by
      show rpxIsCanonical
          (match rpxTrim restCoeffs with
            | [] =>
                match qnfDecEq coeff qnfZero with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail) = true
      cases hTrim : rpxTrim restCoeffs with
      | nil =>
          cases qnfDecEq coeff qnfZero with
          | isTrue _ => rfl
          | isFalse hHeadNonzero =>
              show not (qnfBeq coeff qnfZero) = true
              exact congrArg not (qnfBeqFalseOfNe hHeadNonzero)
      | cons trimHead trimTail =>
          have ihTail := rpxTrimIsCanonical restCoeffs
          rw [hTrim] at ihTail
          show not (qnfBeq (rpxLastOrZero (trimHead :: trimTail)) qnfZero) = true
          exact ihTail

/-! ## Structural Boolean equality with beq-iff-eq (T1) -/

/-- Structural Boolean equality on coefficient lists — componentwise `qnfBeq`, length-sensitive.  Because
`qnfBeq` is rational equality, `rpxBeq` is polynomial equality on equal-length representatives. -/
def rpxBeq : List QnfRat → List QnfRat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftTail, rightHead :: rightTail =>
      qnfBeq leftHead rightHead && rpxBeq leftTail rightTail

/-- `rpxBeq` is reflexively true — each component comparator is (`qnfBeqSelfIsTrue`). -/
theorem rpxBeqSelfIsTrue : ∀ coeffs : List QnfRat, rpxBeq coeffs coeffs = true
  | [] => rfl
  | coeff :: restCoeffs =>
      (congrArg (· && rpxBeq restCoeffs restCoeffs) (qnfBeqSelfIsTrue coeff)).trans
        (rpxBeqSelfIsTrue restCoeffs)

/-- `rpxBeq` at `true` gives list equality — length-mismatch arms refute on the `Bool`, the cons/cons arm
lifts the head equality (`qnfBeqIffEq`) and the tail equality (induction) through `List.cons`. -/
theorem rpxEqOfBeqTrue : ∀ {leftCoeffs rightCoeffs : List QnfRat},
    rpxBeq leftCoeffs rightCoeffs = true → leftCoeffs = rightCoeffs
  | [], [], _ => rfl
  | [], _ :: _, isBeqTrue => Bool.noConfusion isBeqTrue
  | _ :: _, [], isBeqTrue => Bool.noConfusion isBeqTrue
  | leftHead :: _leftTail, rightHead :: rightTail, isBeqTrue =>
      (congrArg (leftHead :: ·) (rpxEqOfBeqTrue (qnfBoolAndTrueGivesRight isBeqTrue))).trans
        (congrArg (· :: rightTail)
          ((qnfBeqIffEq leftHead rightHead).mp (qnfBoolAndTrueGivesLeft isBeqTrue)))

/-- **Structural `==` IS list equality** — the T1 acceptance bar. -/
theorem rpxBeqIffEq (leftCoeffs rightCoeffs : List QnfRat) :
    rpxBeq leftCoeffs rightCoeffs = true ↔ leftCoeffs = rightCoeffs :=
  Iff.intro rpxEqOfBeqTrue
    (fun areEqual =>
      Eq.rec (motive := fun target _ => rpxBeq leftCoeffs target = true)
        (rpxBeqSelfIsTrue leftCoeffs) areEqual)

/-! ## The polynomial ring operations (structural on the ascending coefficient list) (T2) -/

/-- Entrywise coefficient sum with tail padding: `(c₀+d₀) + (c₁+d₁)·x + ⋯`, the longer polynomial's tail
carried through unchanged. -/
def rpxAdd : List QnfRat → List QnfRat → List QnfRat
  | [], rightPoly => rightPoly
  | leftPoly, [] => leftPoly
  | leftHead :: leftTail, rightHead :: rightTail =>
      qnfAdd leftHead rightHead :: rpxAdd leftTail rightTail

/-- Scalar multiple: `scalar·c₀ + scalar·c₁·x + ⋯`. -/
def rpxScale (scalar : QnfRat) : List QnfRat → List QnfRat
  | [] => []
  | coeff :: restCoeffs => qnfMul scalar coeff :: rpxScale scalar restCoeffs

/-- Polynomial product by convolution: `(c₀ + x·p')·q = c₀·q + x·(p'·q)`, the shift `x·(·)` realized by a
leading `qnfZero`. -/
def rpxMul : List QnfRat → List QnfRat → List QnfRat
  | [], _ => []
  | leftHead :: leftTail, rightPoly =>
      rpxAdd (rpxScale leftHead rightPoly) (qnfZero :: rpxMul leftTail rightPoly)

/-- Coefficientwise negation. -/
def rpxNeg : List QnfRat → List QnfRat
  | [] => []
  | coeff :: restCoeffs => qnfNeg coeff :: rpxNeg restCoeffs

/-- Polynomial difference: `leftPoly + (-rightPoly)`, the shape a Euclidean-division remainder takes. -/
def rpxSub (leftPoly rightPoly : List QnfRat) : List QnfRat :=
  rpxAdd leftPoly (rpxNeg rightPoly)

/-- Horner evaluation of the ascending coefficient list at `point`: `c₀ + point·(c₁ + point·(⋯))`. -/
def rpxEval (point : QnfRat) : List QnfRat → QnfRat
  | [] => qnfZero
  | coeff :: restCoeffs => qnfAdd coeff (qnfMul point (rpxEval point restCoeffs))

/-! ## Evaluation is a ring homomorphism (PROVEN by structural induction) (T2) -/

/-- **Additivity.**  `eval(p + q) = eval(p) + eval(q)`. -/
theorem rpxEvalAdd (point : QnfRat) :
    ∀ leftPoly rightPoly : List QnfRat,
      rpxEval point (rpxAdd leftPoly rightPoly)
        = qnfAdd (rpxEval point leftPoly) (rpxEval point rightPoly)
  | [], rightPoly => (qnfAddZeroLeft (rpxEval point rightPoly)).symm
  | _ :: _, [] => (qnfAddZeroRight _).symm
  | leftHead :: leftTail, rightHead :: rightTail =>
      (congrArg (fun tailValue => qnfAdd (qnfAdd leftHead rightHead) (qnfMul point tailValue))
          (rpxEvalAdd point leftTail rightTail)).trans
        ((congrArg (qnfAdd (qnfAdd leftHead rightHead))
            (qnfMulLeftDistrib point (rpxEval point leftTail) (rpxEval point rightTail))).trans
          (qnfAddInterchange leftHead rightHead
            (qnfMul point (rpxEval point leftTail)) (qnfMul point (rpxEval point rightTail))))

/-- **Scalar homogeneity.**  `eval(scalar · p) = scalar · eval(p)`. -/
theorem rpxEvalScale (point scalar : QnfRat) :
    ∀ coeffs : List QnfRat, rpxEval point (rpxScale scalar coeffs) = qnfMul scalar (rpxEval point coeffs)
  | [] => (qnfMulZeroRight scalar).symm
  | coeff :: restCoeffs =>
      (congrArg (fun tailValue => qnfAdd (qnfMul scalar coeff) (qnfMul point tailValue))
          (rpxEvalScale point scalar restCoeffs)).trans
        ((congrArg (qnfAdd (qnfMul scalar coeff))
            ((qnfMulAssoc point scalar (rpxEval point restCoeffs)).symm.trans
              ((congrArg (qnfMul · (rpxEval point restCoeffs)) (qnfMulComm point scalar)).trans
                (qnfMulAssoc scalar point (rpxEval point restCoeffs))))).trans
          (qnfMulLeftDistrib scalar coeff (qnfMul point (rpxEval point restCoeffs))).symm)

/-- **Multiplicativity.**  `eval(p × q) = eval(p) × eval(q)` — the discrete-convolution correctness of
`rpxMul`, by induction on the left polynomial. -/
theorem rpxEvalMul (point : QnfRat) :
    ∀ leftPoly rightPoly : List QnfRat,
      rpxEval point (rpxMul leftPoly rightPoly)
        = qnfMul (rpxEval point leftPoly) (rpxEval point rightPoly)
  | [], rightPoly => (qnfMulZeroLeft (rpxEval point rightPoly)).symm
  | leftHead :: leftTail, rightPoly =>
      (rpxEvalAdd point (rpxScale leftHead rightPoly) (qnfZero :: rpxMul leftTail rightPoly)).trans
        ((congrArg (qnfAdd · (rpxEval point (qnfZero :: rpxMul leftTail rightPoly)))
            (rpxEvalScale point leftHead rightPoly)).trans
          ((congrArg (qnfAdd (qnfMul leftHead (rpxEval point rightPoly)))
              ((congrArg (fun tailValue => qnfAdd qnfZero (qnfMul point tailValue))
                  (rpxEvalMul point leftTail rightPoly)).trans
                (qnfAddZeroLeft
                  (qnfMul point (qnfMul (rpxEval point leftTail) (rpxEval point rightPoly)))))).trans
            ((qnfMulRightDistrib leftHead (qnfMul point (rpxEval point leftTail))
                  (rpxEval point rightPoly)).trans
              (congrArg (qnfAdd (qnfMul leftHead (rpxEval point rightPoly)))
                (qnfMulAssoc point (rpxEval point leftTail) (rpxEval point rightPoly)))).symm))

/-- **Evaluation negates.**  `eval(-p) = -eval(p)`. -/
theorem rpxEvalNeg (point : QnfRat) :
    ∀ coeffs : List QnfRat, rpxEval point (rpxNeg coeffs) = qnfNeg (rpxEval point coeffs)
  | [] => qnfNegZero.symm
  | coeff :: restCoeffs =>
      (congrArg (fun tailValue => qnfAdd (qnfNeg coeff) (qnfMul point tailValue))
          (rpxEvalNeg point restCoeffs)).trans
        ((congrArg (qnfAdd (qnfNeg coeff)) (qnfMulNegRight point (rpxEval point restCoeffs))).trans
          (qnfNegAdd coeff (qnfMul point (rpxEval point restCoeffs))).symm)

/-- **Evaluation is subtractive.**  `eval(p − q) = eval(p) − eval(q)`. -/
theorem rpxEvalSub (point : QnfRat) (leftPoly rightPoly : List QnfRat) :
    rpxEval point (rpxSub leftPoly rightPoly)
      = qnfSub (rpxEval point leftPoly) (rpxEval point rightPoly) :=
  (rpxEvalAdd point leftPoly (rpxNeg rightPoly)).trans
    ((congrArg (qnfAdd (rpxEval point leftPoly)) (rpxEvalNeg point rightPoly)).trans
      (qnfSubEqAddNeg (rpxEval point leftPoly) (rpxEval point rightPoly)).symm)

/-! ## Trimming preserves evaluation (soundness of the normal form) -/

/-- **Trimming preserves evaluation.**  `rpxEval point (rpxTrim p) = rpxEval point p`: the dropped trailing
zeros contribute `qnfZero` at every point.  Induction on the list, casing on the trimmed tail and (when
empty) on whether the head is zero. -/
theorem rpxTrimPreservesEval (point : QnfRat) :
    ∀ coeffs : List QnfRat, rpxEval point (rpxTrim coeffs) = rpxEval point coeffs
  | [] => rfl
  | coeff :: restCoeffs => by
      have ihTail : rpxEval point (rpxTrim restCoeffs) = rpxEval point restCoeffs :=
        rpxTrimPreservesEval point restCoeffs
      show rpxEval point
          (match rpxTrim restCoeffs with
            | [] =>
                match qnfDecEq coeff qnfZero with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail)
        = qnfAdd coeff (qnfMul point (rpxEval point restCoeffs))
      cases hTrim : rpxTrim restCoeffs with
      | nil =>
          rw [hTrim] at ihTail
          cases qnfDecEq coeff qnfZero with
          | isTrue hHeadZero =>
              show qnfZero = qnfAdd coeff (qnfMul point (rpxEval point restCoeffs))
              rw [hHeadZero, ← ihTail]
              exact ((qnfAddZeroLeft (qnfMul point (rpxEval point ([] : List QnfRat)))).trans
                (qnfMulZeroRight point)).symm
          | isFalse _ =>
              show qnfAdd coeff (qnfMul point (rpxEval point ([] : List QnfRat)))
                  = qnfAdd coeff (qnfMul point (rpxEval point restCoeffs))
              exact congrArg (fun tailValue => qnfAdd coeff (qnfMul point tailValue)) ihTail
      | cons trimHead trimTail =>
          rw [hTrim] at ihTail
          show qnfAdd coeff (qnfMul point (rpxEval point (trimHead :: trimTail)))
              = qnfAdd coeff (qnfMul point (rpxEval point restCoeffs))
          exact congrArg (fun tailValue => qnfAdd coeff (qnfMul point tailValue)) ihTail

/-! ## The monomial and the quotient term (the field division quotient's leading term) -/

/-- The monomial `coeff · x^degree`: `degree` leading zeros followed by the coefficient. -/
def rpxMonomial (coeff : QnfRat) : Nat → List QnfRat
  | 0 => [coeff]
  | degree + 1 => qnfZero :: rpxMonomial coeff degree

/-- The Euclidean-division quotient term for one reduction step: `(leadDividend · leadDivisor⁻¹) ·
x^(deg dividend − deg divisor)`.  Over the field ℚ the inverse `qnfInv` makes the leading coefficients
cancel exactly — no integral scaling needed. -/
def rpxQuotientTerm (divisor dividend : List QnfRat) : List QnfRat :=
  rpxMonomial (qnfMul (rpxLeadingCoeff dividend) (qnfInv (rpxLeadingCoeff divisor)))
    (rpxDegree dividend - rpxDegree divisor)

/-! ## Euclidean division with remainder (T3) -/

/-- **The division-step reconstruction, at the ℚ level.**  From `D − qt·G = sq·G + Rem` conclude
`D = (qt + sq)·G + Rem` — add `qt·G` back, re-associate, factor by right distributivity. -/
theorem rpxDivStepArith (dividendEval quotientTermEval subQuotientEval divisorEval remainderEval : QnfRat)
    (reducedIdentity :
      qnfSub dividendEval (qnfMul quotientTermEval divisorEval)
        = qnfAdd (qnfMul subQuotientEval divisorEval) remainderEval) :
    dividendEval
      = qnfAdd (qnfMul (qnfAdd quotientTermEval subQuotientEval) divisorEval) remainderEval :=
  (qnfAddSubCancel dividendEval (qnfMul quotientTermEval divisorEval)).symm.trans
    ((congrArg (qnfAdd · (qnfMul quotientTermEval divisorEval)) reducedIdentity).trans
      ((qnfAddComm (qnfAdd (qnfMul subQuotientEval divisorEval) remainderEval)
          (qnfMul quotientTermEval divisorEval)).trans
        ((qnfAddAssoc (qnfMul quotientTermEval divisorEval) (qnfMul subQuotientEval divisorEval)
            remainderEval).symm.trans
          (congrArg (qnfAdd · remainderEval)
            (qnfMulRightDistrib quotientTermEval subQuotientEval divisorEval).symm))))

/-- Euclidean division with remainder over ℚ.  `fuel` bounds the recursion; each step subtracts the
field-scaled leading-term multiple `rpxQuotientTerm divisor dividend · divisor`, producing a TRUE
remainder (no integral pseudo-scaling — every nonzero leading coefficient inverts via `qnfInv`). -/
def rpxDivMod : Nat → List QnfRat → List QnfRat → (List QnfRat × List QnfRat)
  | 0, _, dividend => ([], dividend)
  | fuel + 1, divisor, dividend =>
      match Nat.decLt (rpxDegree dividend) (rpxDegree divisor) with
      | isTrue _ => ([], dividend)
      | isFalse _ =>
          let quotientTerm := rpxQuotientTerm divisor dividend
          let subResult := rpxDivMod fuel divisor (rpxSub dividend (rpxMul quotientTerm divisor))
          (rpxAdd quotientTerm subResult.1, subResult.2)

/-- **THE DIVISION SPEC — reconstruction at every fuel.**  `eval(dividend) = eval(quotient)·eval(divisor)
+ eval(remainder)` for every fuel — the reduce-invariant `remainder + divisor·accumulatedQuotient =
dividend`, resting only on the ring homomorphism (`rpxEvalSub`/`rpxEvalMul`/`rpxEvalAdd`), hence holding
REGARDLESS of whether the fuel sufficed.  This decouples division correctness from termination. -/
theorem rpxDivModReconstructs (point : QnfRat) :
    ∀ (fuel : Nat) (divisor dividend : List QnfRat),
      rpxEval point dividend
        = qnfAdd (qnfMul (rpxEval point (rpxDivMod fuel divisor dividend).1) (rpxEval point divisor))
            (rpxEval point (rpxDivMod fuel divisor dividend).2)
  | 0, divisor, dividend => by
      show rpxEval point dividend
        = qnfAdd (qnfMul (rpxEval point ([] : List QnfRat)) (rpxEval point divisor))
            (rpxEval point dividend)
      exact (qnfAddZeroLeft (rpxEval point dividend)).symm.trans
        (congrArg (qnfAdd · (rpxEval point dividend)) (qnfMulZeroLeft (rpxEval point divisor)).symm)
  | fuel + 1, divisor, dividend => by
      dsimp only [rpxDivMod]
      cases Nat.decLt (rpxDegree dividend) (rpxDegree divisor) with
      | isTrue _ =>
          show rpxEval point dividend
            = qnfAdd (qnfMul (rpxEval point ([] : List QnfRat)) (rpxEval point divisor))
                (rpxEval point dividend)
          exact (qnfAddZeroLeft (rpxEval point dividend)).symm.trans
            (congrArg (qnfAdd · (rpxEval point dividend)) (qnfMulZeroLeft (rpxEval point divisor)).symm)
      | isFalse _ =>
          have ihStep := rpxDivModReconstructs point fuel divisor
            (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))
          have reducedIdentity :
              qnfSub (rpxEval point dividend)
                  (qnfMul (rpxEval point (rpxQuotientTerm divisor dividend)) (rpxEval point divisor))
                = qnfAdd
                    (qnfMul (rpxEval point (rpxDivMod fuel divisor
                        (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).1)
                      (rpxEval point divisor))
                    (rpxEval point (rpxDivMod fuel divisor
                        (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).2) := by
            refine Eq.trans ?_ ihStep
            exact ((rpxEvalSub point dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor)).trans
              (congrArg (qnfSub (rpxEval point dividend))
                (rpxEvalMul point (rpxQuotientTerm divisor dividend) divisor))).symm
          refine Eq.trans (rpxDivStepArith (rpxEval point dividend)
            (rpxEval point (rpxQuotientTerm divisor dividend))
            (rpxEval point (rpxDivMod fuel divisor
              (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).1)
            (rpxEval point divisor)
            (rpxEval point (rpxDivMod fuel divisor
              (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).2)
            reducedIdentity) ?_
          exact congrArg
            (fun leadFactor =>
              qnfAdd (qnfMul leadFactor (rpxEval point divisor))
                (rpxEval point (rpxDivMod fuel divisor
                  (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).2))
            (rpxEvalAdd point (rpxQuotientTerm divisor dividend)
              (rpxDivMod fuel divisor
                (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).1).symm

/-- **Zero remainder means exact division.**  When the remainder trims to the zero polynomial,
`eval(dividend) = eval(quotient)·eval(divisor)` at every point — the divisor divides the dividend. -/
theorem rpxDividesEvalMultiple (point : QnfRat) (fuel : Nat) (divisor dividend : List QnfRat)
    (remainderTrimsToZero : rpxTrim (rpxDivMod fuel divisor dividend).2 = []) :
    rpxEval point dividend
      = qnfMul (rpxEval point (rpxDivMod fuel divisor dividend).1) (rpxEval point divisor) :=
  (rpxDivModReconstructs point fuel divisor dividend).trans
    ((congrArg
        (qnfAdd (qnfMul (rpxEval point (rpxDivMod fuel divisor dividend).1) (rpxEval point divisor)))
        ((rpxTrimPreservesEval point (rpxDivMod fuel divisor dividend).2).symm.trans
          (congrArg (rpxEval point) remainderTrimsToZero))).trans
      (qnfAddZeroRight
        (qnfMul (rpxEval point (rpxDivMod fuel divisor dividend).1) (rpxEval point divisor))))

/-! ## The Euclidean GCD (T4) -/

/-- The remainder of dividing `dividend` by `divisor` (the second component of Euclidean division). -/
def rpxRemainder (fuel : Nat) (divisor dividend : List QnfRat) : List QnfRat :=
  (rpxDivMod fuel divisor dividend).2

/-- **The remainder vanishes at every common root.**  If `dividend` and `divisor` both evaluate to `qnfZero`
at a point, so does their remainder — read off `eval(dividend) = eval(quotient)·eval(divisor) +
eval(remainder)`: the product collapses on `eval(divisor) = 0`, leaving `eval(remainder) =
eval(dividend) = 0`. -/
theorem rpxRemainderVanishesAtCommonRoot (point : QnfRat) (fuel : Nat) (divisor dividend : List QnfRat)
    (dividendVanishes : rpxEval point dividend = qnfZero)
    (divisorVanishes : rpxEval point divisor = qnfZero) :
    rpxEval point (rpxRemainder fuel divisor dividend) = qnfZero := by
  show rpxEval point (rpxDivMod fuel divisor dividend).2 = qnfZero
  have productZero :
      qnfMul (rpxEval point (rpxDivMod fuel divisor dividend).1) (rpxEval point divisor) = qnfZero :=
    (congrArg (qnfMul (rpxEval point (rpxDivMod fuel divisor dividend).1)) divisorVanishes).trans
      (qnfMulZeroRight (rpxEval point (rpxDivMod fuel divisor dividend).1))
  have collapse :
      qnfAdd (qnfMul (rpxEval point (rpxDivMod fuel divisor dividend).1) (rpxEval point divisor))
          (rpxEval point (rpxDivMod fuel divisor dividend).2)
        = rpxEval point (rpxDivMod fuel divisor dividend).2 :=
    (congrArg (qnfAdd · (rpxEval point (rpxDivMod fuel divisor dividend).2)) productZero).trans
      (qnfAddZeroLeft (rpxEval point (rpxDivMod fuel divisor dividend).2))
  exact collapse.symm.trans
    ((rpxDivModReconstructs point fuel divisor dividend).symm.trans dividendVanishes)

/-- The Euclidean GCD over ℚ[x]: `gcd(primary, secondary) = gcd(secondary, remainder(primary, secondary))`
until the second argument trims to the zero polynomial.  `fuel` bounds the recursion structurally.  Over
the field ℚ the remainder is exact, so this is the textbook Euclidean algorithm — no pseudo-scaling. -/
def rpxGcd : Nat → List QnfRat → List QnfRat → List QnfRat
  | 0, primary, _ => primary
  | fuel + 1, primary, secondary =>
      match rpxTrim secondary with
      | [] => primary
      | _ :: _ => rpxGcd fuel secondary (rpxRemainder fuel secondary primary)

/-- **The GCD vanishes at every common root.**  If `primary` and `secondary` both vanish at a point, so
does `rpxGcd fuel primary secondary` — induction on fuel; the base returns `primary` (which vanishes) and
the Euclidean step preserves both vanishings through `rpxRemainderVanishesAtCommonRoot`. -/
theorem rpxGcdVanishesAtCommonRoot (point : QnfRat) :
    ∀ (fuel : Nat) (primary secondary : List QnfRat),
      rpxEval point primary = qnfZero → rpxEval point secondary = qnfZero →
      rpxEval point (rpxGcd fuel primary secondary) = qnfZero
  | 0, _, _, primaryVanishes, _ => primaryVanishes
  | fuel + 1, primary, secondary, primaryVanishes, secondaryVanishes => by
      dsimp only [rpxGcd]
      cases rpxTrim secondary with
      | nil => exact primaryVanishes
      | cons _ _ =>
          exact rpxGcdVanishesAtCommonRoot point fuel secondary
            (rpxRemainder fuel secondary primary) secondaryVanishes
            (rpxRemainderVanishesAtCommonRoot point fuel secondary primary
              primaryVanishes secondaryVanishes)

/-- **`gcd(f, 0) = f`.**  When the second argument is the zero polynomial, the GCD is the first argument —
the Euclidean terminating case (`rpxTrim [] = []`), definitional. -/
theorem rpxGcdRightZero (fuel : Nat) (primary : List QnfRat) :
    rpxGcd (fuel + 1) primary [] = primary := rfl

/-! ## The linear factor and the shared-root bridge (the eigenvalue-sharing shadow) -/

/-- The constant polynomial `1` evaluates to `1` at every point. -/
theorem rpxEvalOne (point : QnfRat) : rpxEval point [qnfOne] = qnfOne :=
  (congrArg (qnfAdd qnfOne) (qnfMulZeroRight point)).trans (qnfAddZeroRight qnfOne)

/-- The linear factor `x − root`, i.e. the ascending list `[-root, 1]`. -/
def rpxLinearFactor (root : QnfRat) : List QnfRat := [qnfNeg root, qnfOne]

/-- **Linear factor evaluates to the shift.**  `eval_point(x − root) = point − root`. -/
theorem rpxEvalLinearFactor (point root : QnfRat) :
    rpxEval point (rpxLinearFactor root) = qnfSub point root :=
  (congrArg (fun tailValue => qnfAdd (qnfNeg root) (qnfMul point tailValue)) (rpxEvalOne point)).trans
    ((congrArg (qnfAdd (qnfNeg root)) (qnfMulOneRight point)).trans
      ((qnfAddComm (qnfNeg root) point).trans (qnfSubEqAddNeg point root).symm))

/-- **The linear factor vanishes at its root.**  `eval_root(x − root) = 0`. -/
theorem rpxLinearFactorVanishesAtRoot (root : QnfRat) :
    rpxEval root (rpxLinearFactor root) = qnfZero :=
  (rpxEvalLinearFactor root root).trans
    ((qnfSubEqAddNeg root root).trans (qnfAddNegRight root))

/-- **Root theorem, factor ⟹ root.**  Any multiple of `x − root` vanishes at `root`. -/
theorem rpxLinearFactorRootAnnihilatesMultiple (root : QnfRat) (cofactor : List QnfRat) :
    rpxEval root (rpxMul (rpxLinearFactor root) cofactor) = qnfZero :=
  (rpxEvalMul root (rpxLinearFactor root) cofactor).trans
    ((congrArg (qnfMul · (rpxEval root cofactor)) (rpxLinearFactorVanishesAtRoot root)).trans
      (qnfMulZeroLeft (rpxEval root cofactor)))

/-- **A shared linear factor is seen by the GCD.**  If `x − root` divides both inputs, the GCD vanishes at
`root` — the polynomial shadow of "two matrices share the eigenvalue `root`". -/
theorem rpxGcdSeesSharedLinearFactor (root : QnfRat) (fuel : Nat)
    (cofactorPrimary cofactorSecondary : List QnfRat) :
    rpxEval root
        (rpxGcd fuel (rpxMul (rpxLinearFactor root) cofactorPrimary)
          (rpxMul (rpxLinearFactor root) cofactorSecondary))
      = qnfZero :=
  rpxGcdVanishesAtCommonRoot root fuel
    (rpxMul (rpxLinearFactor root) cofactorPrimary)
    (rpxMul (rpxLinearFactor root) cofactorSecondary)
    (rpxLinearFactorRootAnnihilatesMultiple root cofactorPrimary)
    (rpxLinearFactorRootAnnihilatesMultiple root cofactorSecondary)

/-! ## Groundings (T5)

Closed-value kernel pins: the whole `qnfNormalize`/`qnfInv`/Euclid pipeline reduces inside the kernel, so
each pin is a bare `rfl`.  The raised recursion depth covers the composed counting-divider reductions. -/

set_option maxRecDepth 8192

/-- Fire: `x² − 1` divided by `x − 1` leaves remainder zero (the divisor divides exactly). -/
theorem rpxFireDifferenceOfSquaresRemainderZero :
    rpxTrim (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).2 = [] :=
  rfl

/-- Fire: the quotient of `(x² − 1) ÷ (x − 1)` is `x + 1`. -/
theorem rpxFireDifferenceOfSquaresQuotient :
    rpxBeq (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).1
        [qnfOfInt 1, qnfOfInt 1] = true :=
  rfl

/-- Fire: `x² + 1` divided by `x − 1` has quotient `x + 1`. -/
theorem rpxFireOnePlusSquareQuotient :
    rpxBeq (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]).1
        [qnfOfInt 1, qnfOfInt 1] = true :=
  rfl

/-- Fire: `x² + 1` divided by `x − 1` leaves the constant remainder `2` (`= 1² + 1` at the root `1`). -/
theorem rpxFireOnePlusSquareRemainder :
    rpxBeq (rpxTrim (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]).2)
        [qnfOfInt 2] = true :=
  rfl

/-- Fire (rational coefficients): `2x` divided by `3x` has quotient the constant `2/3`, remainder zero —
the ℤ[x] pseudo-divider could not name `2/3`; the field divider does via `qnfInv`. -/
theorem rpxFireRationalQuotientTwoThirds :
    rpxBeq (rpxDivMod 2 [qnfOfInt 0, qnfOfInt 3] [qnfOfInt 0, qnfOfInt 2]).1
        [qnfNormalize { numerator := 2, denominatorPredecessor := 2 }] = true :=
  rfl

/-- Fire: `2x` divided by `3x` leaves remainder zero. -/
theorem rpxFireRationalRemainderZero :
    rpxTrim (rpxDivMod 2 [qnfOfInt 0, qnfOfInt 3] [qnfOfInt 0, qnfOfInt 2]).2 = [] :=
  rfl

/-- Fire (reconstruction at a point): on `x² − 1 = (x−1)(x+1)` at `x = 4`,
`eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder)`, the closed-value shadow of
`rpxDivModReconstructs`. -/
theorem rpxFireReconstructsAtFour :
    rpxEval (qnfOfInt 4) [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
      = qnfAdd
          (qnfMul
            (rpxEval (qnfOfInt 4)
              (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).1)
            (rpxEval (qnfOfInt 4) [qnfOfInt (-1), qnfOfInt 1]))
          (rpxEval (qnfOfInt 4)
            (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).2) :=
  rpxDivModReconstructs (qnfOfInt 4) 3 [qnfOfInt (-1), qnfOfInt 1]
    [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]

/-- Fire: the GCD of `x² − 1 = (x−1)(x+1)` and `x² − 2x + 1 = (x−1)²` vanishes at the shared root `1`
(their common factor `x − 1`), an instance of `rpxGcdVanishesAtCommonRoot`. -/
theorem rpxFireGcdSharesRootAtOne :
    qnfBeq
        (rpxEval (qnfOfInt 1)
          (rpxGcd 5 [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
            [qnfOfInt 1, qnfOfInt (-2), qnfOfInt 1]))
        qnfZero
      = true :=
  rfl

/-- Fire: that GCD is the degree-1 common factor `x − 1` (up to a scalar). -/
theorem rpxFireGcdCommonFactorDegree :
    rpxDegree
        (rpxGcd 5 [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt 1, qnfOfInt (-2), qnfOfInt 1])
      = 1 :=
  rfl

/-- Fire (canonicality): a trailing-zero list is not canonical, while its trim is. -/
theorem rpxFireTrailingZeroNotCanonical :
    rpxIsCanonical [qnfOfInt 3, qnfOfInt 0] = false :=
  rfl

theorem rpxFireTrimmedIsCanonical :
    rpxIsCanonical (rpxTrim [qnfOfInt 3, qnfOfInt 0]) = true :=
  rfl

/-! ## Content marker -/

/-- ℚ[x] Euclidean division is decided: `rpxDivMod` with the reconstruction invariant
`eval(dividend) = eval(quotient)·eval(divisor) + eval(remainder)` proved at every fuel
(`rpxDivModReconstructs`), the exact-division corollary (`rpxDividesEvalMultiple`), evaluation as a ring
homomorphism (`rpxEvalAdd`/`rpxEvalScale`/`rpxEvalMul`/`rpxEvalNeg`/`rpxEvalSub`), and the Euclidean GCD
(`rpxGcd`) capturing every common root (`rpxGcdVanishesAtCommonRoot`) with the shared-linear-factor bridge and
`gcd(f, 0) = f`. The field divider names rational quotient coefficients via `qnfInv`, unlike the ℤ[x]
pseudo-divider. The remainder degree bound, "gcd divides both", and Bezout are decided downstream
(`rpdHasRemainderDegreeBound`, `rpeHasGcdDividesBoth`, `rbzHasBezoutIdentity`). -/
def rpxHasEuclideanDivision : Bool := true

end FX1Poly.ComputerAlgebra
