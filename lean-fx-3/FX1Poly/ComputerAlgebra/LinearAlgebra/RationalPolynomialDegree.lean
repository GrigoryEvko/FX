import FX1Poly.ComputerAlgebra.LinearAlgebra.RationalPolynomial
import FX1Poly.ComputerAlgebra.Number.NatModularReduction

/-! # RationalPolynomialDegree — the ℚ[x] degree-based termination bound

`RationalPolynomial` shipped Euclidean division (`rpxDivMod`) with the reconstruction invariant proved at every
fuel, but left the degree half open: the remainder degree bound and "gcd divides both" rest on fuel adequacy —
that the recursion reached the zero-remainder leaf. This module supplies that termination bound over the field
ℚ, with the field-specific leading-term cancellation (the quotient term is `leadDividend · leadDivisor⁻¹ · x^Δ`,
so the leading coefficients cancel exactly via `qnfInvMulCancels`).

The step lemma `rpdStepTrimLengthDecreases` shows one Euclidean division step strictly drops the trimmed length
(the top coefficient cancels, `rpdStepTopCoeffCancels`, and everything above vanishes). Fuel adequacy
`rpdRemainderAdequate` then shows: with `(rpxTrim dividend).length ≤ fuel` and a nonzero divisor, the remainder
either trims to zero or has degree strictly below the divisor's. At `fuel = dividend.length` (adequate since
`(rpxTrim dividend).length ≤ dividend.length`) this gives `rpdDivModRemainderDegree`. The exact single-step
trim-level reconstruction (`rpdStepReconstructsTrim`, on `rpdTrimEqOfCoeffEq`) is the coefficient-level content
the committed eval-only reconstruction does not provide — the foundation for "gcd divides both", decided
downstream (`rpeHasGcdDividesBoth`).

The coefficient calculus (`rpxCoeff` with its ring-homomorphism lemmas, the monomial-product shift, and the
past-length / trim-length bounds) supports these proofs. Every definition is structural on the coefficient list
and position; arithmetic routes through the shipped `qnf*` field laws and core `Nat` order lemmas. No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or `WellFounded.fix`.
Per-declaration audit twin in the matching `FX1PolyAudit` path. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Small Nat helpers -/

/-- `smaller ≤ larger → (larger − smaller) + smaller = larger` — the commuted `natAddSubOfLe`. -/
theorem rpdNatSubAddCancel {smaller larger : Nat} (isLe : smaller ≤ larger) :
    (larger - smaller) + smaller = larger :=
  (Nat.add_comm (larger - smaller) smaller).trans (natAddSubOfLe isLe)

/-! ## The positional coefficient accessor -/

/-- `rpxCoeff coeffs n` — the coefficient of `xⁿ` in the ascending list `coeffs`, or `qnfZero` past the
end. -/
def rpxCoeff : List QnfRat → Nat → QnfRat
  | [], _ => qnfZero
  | coeff :: _, 0 => coeff
  | _ :: restCoeffs, position + 1 => rpxCoeff restCoeffs position

/-! ## Each coefficient is a ring homomorphism -/

/-- **Scaling acts coefficientwise.**  `rpxCoeff (scalar · p) n = scalar · rpxCoeff p n`. -/
theorem rpxCoeffScale (scalar : QnfRat) :
    ∀ (coeffs : List QnfRat) (position : Nat),
      rpxCoeff (rpxScale scalar coeffs) position = qnfMul scalar (rpxCoeff coeffs position)
  | [], _ => (qnfMulZeroRight scalar).symm
  | _ :: _, 0 => rfl
  | _ :: restCoeffs, position + 1 => rpxCoeffScale scalar restCoeffs position

/-- **Addition acts coefficientwise.**  `rpxCoeff (p + q) n = rpxCoeff p n + rpxCoeff q n`. -/
theorem rpxCoeffAdd :
    ∀ (leftPoly rightPoly : List QnfRat) (position : Nat),
      rpxCoeff (rpxAdd leftPoly rightPoly) position
        = qnfAdd (rpxCoeff leftPoly position) (rpxCoeff rightPoly position)
  | [], rightPoly, position => (qnfAddZeroLeft (rpxCoeff rightPoly position)).symm
  | _ :: _, [], position => (qnfAddZeroRight (rpxCoeff (_ :: _) position)).symm
  | _ :: _, _ :: _, 0 => rfl
  | _ :: leftTail, _ :: rightTail, position + 1 => rpxCoeffAdd leftTail rightTail position

/-- **Negation acts coefficientwise.**  `rpxCoeff (-p) n = -(rpxCoeff p n)`. -/
theorem rpxCoeffNeg :
    ∀ (coeffs : List QnfRat) (position : Nat),
      rpxCoeff (rpxNeg coeffs) position = qnfNeg (rpxCoeff coeffs position)
  | [], _ => qnfNegZero.symm
  | _ :: _, 0 => rfl
  | _ :: restCoeffs, position + 1 => rpxCoeffNeg restCoeffs position

/-- **Subtraction acts coefficientwise.**  `rpxCoeff (p − q) n = rpxCoeff p n − rpxCoeff q n`. -/
theorem rpxCoeffSub (leftPoly rightPoly : List QnfRat) (position : Nat) :
    rpxCoeff (rpxSub leftPoly rightPoly) position
      = qnfSub (rpxCoeff leftPoly position) (rpxCoeff rightPoly position) :=
  (rpxCoeffAdd leftPoly (rpxNeg rightPoly) position).trans
    ((congrArg (qnfAdd (rpxCoeff leftPoly position)) (rpxCoeffNeg rightPoly position)).trans
      (qnfSubEqAddNeg (rpxCoeff leftPoly position) (rpxCoeff rightPoly position)).symm)

/-! ## The monomial-times-polynomial coefficient shift (the leading-term-cancellation lever) -/

/-- The one-element zero polynomial reads `qnfZero` at every position. -/
theorem rpdCoeffSingletonZero : ∀ position : Nat, rpxCoeff [qnfZero] position = qnfZero
  | 0 => rfl
  | _ + 1 => rfl

/-- **Multiplying by a monomial shifts and scales coefficients.**  `rpxCoeff (coeff · x^degree · poly)
(position + degree) = coeff · rpxCoeff poly position`.  By induction on `degree` — the base case is the
`rpxMul` convolution `rpxAdd (rpxScale coeff poly) [qnfZero]`, and each successive degree prepends a
`qnfZero` (a `rpxScale qnfZero poly` summand that annihilates) and consumes one position. -/
theorem rpxCoeffMonomialMul (coeff : QnfRat) (poly : List QnfRat) (position : Nat) :
    ∀ degree : Nat,
      rpxCoeff (rpxMul (rpxMonomial coeff degree) poly) (position + degree)
        = qnfMul coeff (rpxCoeff poly position)
  | 0 => by
      show rpxCoeff (rpxAdd (rpxScale coeff poly) [qnfZero]) position = qnfMul coeff (rpxCoeff poly position)
      rw [rpxCoeffAdd, rpxCoeffScale, rpdCoeffSingletonZero, qnfAddZeroRight]
  | degree + 1 => by
      show rpxCoeff (rpxAdd (rpxScale qnfZero poly) (qnfZero :: rpxMul (rpxMonomial coeff degree) poly))
             (position + degree + 1) = qnfMul coeff (rpxCoeff poly position)
      rw [rpxCoeffAdd, rpxCoeffScale, qnfMulZeroLeft, qnfAddZeroLeft]
      show rpxCoeff (rpxMul (rpxMonomial coeff degree) poly) (position + degree)
             = qnfMul coeff (rpxCoeff poly position)
      exact rpxCoeffMonomialMul coeff poly position degree

/-- **A monomial with a zero scalar multiplies to the zero polynomial coefficientwise.**  Used for the
zero-dividend leaf: a vanishing leading coefficient makes the whole quotient-term product vanish. -/
theorem rpdCoeffMonomialZeroMulZero :
    ∀ (degree : Nat) (divisor : List QnfRat) (position : Nat),
      rpxCoeff (rpxMul (rpxMonomial qnfZero degree) divisor) position = qnfZero
  | 0, divisor, position => by
      show rpxCoeff (rpxAdd (rpxScale qnfZero divisor) [qnfZero]) position = qnfZero
      rw [rpxCoeffAdd, rpxCoeffScale, qnfMulZeroLeft, rpdCoeffSingletonZero, qnfAddZeroLeft]
  | degree + 1, divisor, position => by
      show rpxCoeff (rpxAdd (rpxScale qnfZero divisor)
             (qnfZero :: rpxMul (rpxMonomial qnfZero degree) divisor)) position = qnfZero
      rw [rpxCoeffAdd, rpxCoeffScale, qnfMulZeroLeft, qnfAddZeroLeft]
      cases position with
      | zero => rfl
      | succ priorPosition =>
          show rpxCoeff (rpxMul (rpxMonomial qnfZero degree) divisor) priorPosition = qnfZero
          exact rpdCoeffMonomialZeroMulZero degree divisor priorPosition

/-! ## Coefficient bounds: reading past the length and trimming agreement -/

/-- **Past the length, every coefficient is zero.**  `coeffs.length ≤ position → rpxCoeff coeffs position =
qnfZero`. -/
theorem rpxCoeffPastLength :
    ∀ (coeffs : List QnfRat) (position : Nat),
      coeffs.length ≤ position → rpxCoeff coeffs position = qnfZero
  | [], _, _ => rfl
  | _ :: _, 0, hLe => absurd hLe (Nat.not_succ_le_zero _)
  | _ :: restCoeffs, position + 1, hLe =>
      rpxCoeffPastLength restCoeffs position (Nat.le_of_succ_le_succ hLe)

/-- **Trimming trailing zeros never changes a coefficient.**  `rpxCoeff (rpxTrim p) k = rpxCoeff p k` for
every position `k`. -/
theorem rpxCoeffTrimAgree :
    ∀ (coeffs : List QnfRat) (position : Nat),
      rpxCoeff (rpxTrim coeffs) position = rpxCoeff coeffs position
  | [], _ => rfl
  | coeff :: restCoeffs, position => by
      show rpxCoeff
          (match rpxTrim restCoeffs with
            | [] =>
                match qnfDecEq coeff qnfZero with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail) position
        = rpxCoeff (coeff :: restCoeffs) position
      cases hTrim : rpxTrim restCoeffs with
      | nil =>
          cases qnfDecEq coeff qnfZero with
          | isTrue hHeadZero =>
              cases position with
              | zero => exact hHeadZero.symm
              | succ priorPosition =>
                  have ihTail := rpxCoeffTrimAgree restCoeffs priorPosition
                  rw [hTrim] at ihTail
                  exact ihTail
          | isFalse _ =>
              cases position with
              | zero => rfl
              | succ priorPosition =>
                  have ihTail := rpxCoeffTrimAgree restCoeffs priorPosition
                  rw [hTrim] at ihTail
                  exact ihTail
      | cons trimHead trimTail =>
          cases position with
          | zero => rfl
          | succ priorPosition =>
              have ihTail := rpxCoeffTrimAgree restCoeffs priorPosition
              rw [hTrim] at ihTail
              exact ihTail

/-- **At or above the trimmed length, the coefficient is zero.**  `(rpxTrim p).length ≤ position →
rpxCoeff p position = qnfZero`. -/
theorem rpxCoeffZeroFromTrimLength (coeffs : List QnfRat) (position : Nat)
    (isTrimLengthLe : (rpxTrim coeffs).length ≤ position) : rpxCoeff coeffs position = qnfZero :=
  (rpxCoeffTrimAgree coeffs position).symm.trans
    (rpxCoeffPastLength (rpxTrim coeffs) position isTrimLengthLe)

/-! ## The leading coefficient is the coefficient at the degree position -/

/-- Reading the original list at index `(rpxTrim coeffs).length − 1` returns the last surviving
coefficient `rpxLastOrZero (rpxTrim coeffs)`. -/
theorem rpxCoeffTrimLengthEqLastOrZero :
    ∀ coeffs : List QnfRat,
      rpxCoeff coeffs ((rpxTrim coeffs).length - 1) = rpxLastOrZero (rpxTrim coeffs)
  | [] => rfl
  | coeff :: restCoeffs => by
      show rpxCoeff (coeff :: restCoeffs)
          ((match rpxTrim restCoeffs with
            | [] =>
                match qnfDecEq coeff qnfZero with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail).length - 1)
        = rpxLastOrZero
            (match rpxTrim restCoeffs with
              | [] =>
                  match qnfDecEq coeff qnfZero with
                  | isTrue _ => []
                  | isFalse _ => [coeff]
              | trimHead :: trimTail => coeff :: trimHead :: trimTail)
      cases hTrim : rpxTrim restCoeffs with
      | nil =>
          cases qnfDecEq coeff qnfZero with
          | isTrue hHeadZero =>
              show rpxCoeff (coeff :: restCoeffs) 0 = qnfZero
              exact hHeadZero
          | isFalse _ => rfl
      | cons trimHead trimTail =>
          have ihTail := rpxCoeffTrimLengthEqLastOrZero restCoeffs
          rw [hTrim] at ihTail
          show rpxCoeff restCoeffs trimTail.length = rpxLastOrZero (trimHead :: trimTail)
          exact ihTail

/-- **The leading coefficient is the coefficient at the degree position.**  `rpxLeadingCoeff p =
rpxCoeff p (rpxDegree p)`. -/
theorem rpxLeadingCoeffEqCoeffDegree (coeffs : List QnfRat) :
    rpxLeadingCoeff coeffs = rpxCoeff coeffs (rpxDegree coeffs) :=
  (rpxCoeffTrimLengthEqLastOrZero coeffs).symm

/-! ## The trim invariant: a nonzero polynomial's degree-position coefficient is nonzero -/

/-- **A trimmed list is empty or ends nonzero.**  `rpxTrim coeffs = [] ∨ rpxLastOrZero (rpxTrim coeffs) ≠
qnfZero`. -/
theorem rpxTrimNilOrLastNonzero :
    ∀ coeffs : List QnfRat, rpxTrim coeffs = [] ∨ rpxLastOrZero (rpxTrim coeffs) ≠ qnfZero
  | [] => Or.inl rfl
  | coeff :: restCoeffs => by
      show (match rpxTrim restCoeffs with
            | [] =>
                match qnfDecEq coeff qnfZero with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail) = []
        ∨ rpxLastOrZero
            (match rpxTrim restCoeffs with
              | [] =>
                  match qnfDecEq coeff qnfZero with
                  | isTrue _ => []
                  | isFalse _ => [coeff]
              | trimHead :: trimTail => coeff :: trimHead :: trimTail) ≠ qnfZero
      cases hTrim : rpxTrim restCoeffs with
      | nil =>
          cases qnfDecEq coeff qnfZero with
          | isTrue _ => exact Or.inl rfl
          | isFalse hHeadNonzero => exact Or.inr hHeadNonzero
      | cons trimHead trimTail =>
          have ihTail := rpxTrimNilOrLastNonzero restCoeffs
          rw [hTrim] at ihTail
          exact Or.inr (ihTail.resolve_left (List.cons_ne_nil trimHead trimTail))

/-- **A nonzero polynomial has a nonzero leading coefficient.**  `rpxTrim coeffs ≠ [] → rpxLeadingCoeff
coeffs ≠ qnfZero`. -/
theorem rpxLeadingCoeffNonzeroWhenNonempty (coeffs : List QnfRat) (isTrimNonempty : rpxTrim coeffs ≠ []) :
    rpxLeadingCoeff coeffs ≠ qnfZero :=
  (rpxTrimNilOrLastNonzero coeffs).resolve_left isTrimNonempty

/-- **The coefficient at the degree position is nonzero for a nonzero polynomial.**  `rpxTrim coeffs ≠ []
→ rpxCoeff coeffs (rpxDegree coeffs) ≠ qnfZero`. -/
theorem rpxCoeffAtDegreeNonzeroWhenNonempty (coeffs : List QnfRat) (isTrimNonempty : rpxTrim coeffs ≠ []) :
    rpxCoeff coeffs (rpxDegree coeffs) ≠ qnfZero :=
  fun coeffIsZero =>
    rpxLeadingCoeffNonzeroWhenNonempty coeffs isTrimNonempty
      ((rpxLeadingCoeffEqCoeffDegree coeffs).trans coeffIsZero)

/-- **A nonzero polynomial's trimmed length is its degree plus one.**  `rpxTrim coeffs ≠ [] →
(rpxTrim coeffs).length = rpxDegree coeffs + 1`. -/
theorem rpxTrimLengthEqDegreeSucc (coeffs : List QnfRat) (isNonempty : rpxTrim coeffs ≠ []) :
    (rpxTrim coeffs).length = rpxDegree coeffs + 1 := by
  cases hTrim : rpxTrim coeffs with
  | nil => exact absurd hTrim isNonempty
  | cons trimHead trimTail =>
      unfold rpxDegree
      rw [hTrim]
      rfl

/-! ## The trimmed-length bound from coefficient vanishing (the honest measure) -/

/-- **Coefficients vanishing from a bound upward force the trimmed length below it.**  If `rpxCoeff coeffs
position = qnfZero` for all `position ≥ bound`, then `(rpxTrim coeffs).length ≤ bound`.  Unlike the degree
form, this needs no positivity on `bound` (the trimmed length can drop to `0`), so it covers a nonzero
constant dividend.  The lever: were `bound < length`, the (nonzero) degree-position coefficient — sitting
at `length − 1 ≥ bound` — would have to vanish. -/
theorem rpdTrimLengthLeOfVanishFrom (coeffs : List QnfRat) (bound : Nat)
    (vanishes : ∀ position : Nat, bound ≤ position → rpxCoeff coeffs position = qnfZero) :
    (rpxTrim coeffs).length ≤ bound := by
  cases Nat.lt_or_ge bound (rpxTrim coeffs).length with
  | inr isLengthLe => exact isLengthLe
  | inl isBoundLt =>
      cases hTrim : rpxTrim coeffs with
      | nil =>
          rw [hTrim] at isBoundLt
          exact absurd isBoundLt (Nat.not_lt_zero bound)
      | cons trimHead trimTail =>
          have isTrimNonempty : rpxTrim coeffs ≠ [] := by
            rw [hTrim]; exact List.cons_ne_nil trimHead trimTail
          have hDeg : rpxDegree coeffs = trimTail.length :=
            congrArg (· - 1) (congrArg List.length hTrim)
          rw [hTrim] at isBoundLt
          have coeffZero : rpxCoeff coeffs trimTail.length = qnfZero :=
            vanishes trimTail.length (Nat.le_of_lt_succ isBoundLt)
          have coeffNonzero : rpxCoeff coeffs trimTail.length ≠ qnfZero := by
            rw [← hDeg]
            exact rpxCoeffAtDegreeNonzeroWhenNonempty coeffs isTrimNonempty
          exact absurd coeffZero coeffNonzero

/-- **All coefficients zero forces the trim to nil.**  `(∀ position, rpxCoeff coeffs position = qnfZero) →
rpxTrim coeffs = []` — the trimmed length is `≤ 0` by the vanishing bound. -/
theorem rpdTrimNilOfAllCoeffsZero (coeffs : List QnfRat)
    (allZero : ∀ position : Nat, rpxCoeff coeffs position = qnfZero) : rpxTrim coeffs = [] := by
  have lenLe : (rpxTrim coeffs).length ≤ 0 :=
    rpdTrimLengthLeOfVanishFrom coeffs 0 (fun position _ => allZero position)
  cases hTrim : rpxTrim coeffs with
  | nil => rfl
  | cons trimHead trimTail =>
      rw [hTrim] at lenLe
      exact absurd lenLe (Nat.not_succ_le_zero trimTail.length)

/-- **A nil trim reads zero at every coefficient.**  `rpxTrim coeffs = [] → rpxCoeff coeffs position =
qnfZero`. -/
theorem rpdCoeffZeroOfTrimNil (coeffs : List QnfRat) (position : Nat)
    (trimNil : rpxTrim coeffs = []) : rpxCoeff coeffs position = qnfZero :=
  (rpxCoeffTrimAgree coeffs position).symm.trans
    (by rw [trimNil]; rfl)

/-- **Trimming never lengthens.**  `(rpxTrim coeffs).length ≤ coeffs.length`. -/
theorem rpdTrimLengthLe : ∀ coeffs : List QnfRat, (rpxTrim coeffs).length ≤ coeffs.length
  | [] => Nat.le_refl 0
  | coeff :: restCoeffs => by
      show (match rpxTrim restCoeffs with
            | [] =>
                match qnfDecEq coeff qnfZero with
                | isTrue _ => []
                | isFalse _ => [coeff]
            | trimHead :: trimTail => coeff :: trimHead :: trimTail).length
        ≤ (coeff :: restCoeffs).length
      cases hTrim : rpxTrim restCoeffs with
      | nil =>
          cases qnfDecEq coeff qnfZero with
          | isTrue _ => exact Nat.zero_le _
          | isFalse _ =>
              show ([coeff]).length ≤ (coeff :: restCoeffs).length
              exact Nat.succ_le_succ (Nat.zero_le restCoeffs.length)
      | cons trimHead trimTail =>
          have ih := rpdTrimLengthLe restCoeffs
          rw [hTrim] at ih
          show (coeff :: trimHead :: trimTail).length ≤ (coeff :: restCoeffs).length
          exact Nat.succ_le_succ ih

/-! ## The quotient-term product vanishes far above -/

/-- **A monomial-times-polynomial product vanishes past the divisor's degree.**  For `innerPosition` at or
past the divisor's trimmed length, `rpxCoeff (coeff · x^degree · divisor) (innerPosition + degree) =
qnfZero`.  Stated additively to keep the proof free of Nat subtraction. -/
theorem rpxMonomialMulCoeffVanishesFarAbove (coeff : QnfRat) (divisor : List QnfRat)
    (degree innerPosition : Nat) (isFarInner : (rpxTrim divisor).length ≤ innerPosition) :
    rpxCoeff (rpxMul (rpxMonomial coeff degree) divisor) (innerPosition + degree) = qnfZero :=
  (rpxCoeffMonomialMul coeff divisor innerPosition degree).trans
    (by rw [rpxCoeffZeroFromTrimLength divisor innerPosition isFarInner]; exact qnfMulZeroRight coeff)

/-! ## T1 — the division step's leading-term cancellation and strict trimmed-length decrease -/

/-- **The division step annihilates the dividend's top coefficient.**  When `rpxDegree divisor ≤ rpxDegree
dividend` and the divisor is nonzero (`rpxLeadingCoeff divisor ≠ qnfZero`), the replacement dividend
`dividend − (leadDividend · leadDivisor⁻¹ · x^Δ) · divisor` has coefficient `qnfZero` at position `rpxDegree
dividend`: the quotient-term product's top coefficient is `(leadDividend · leadDivisor⁻¹) · leadDivisor =
leadDividend` (field cancellation via `qnfInvMulCancels`), which the dividend's own leading coefficient
cancels. -/
theorem rpdStepTopCoeffCancels (dividend divisor : List QnfRat)
    (divisorLeadNonzero : rpxLeadingCoeff divisor ≠ qnfZero)
    (isDivisorDegreeLe : rpxDegree divisor ≤ rpxDegree dividend) :
    rpxCoeff (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor)) (rpxDegree dividend)
      = qnfZero := by
  have quotientTermTopCoeff :
      rpxCoeff (rpxMul (rpxQuotientTerm divisor dividend) divisor) (rpxDegree dividend)
        = qnfMul (qnfMul (rpxLeadingCoeff dividend) (qnfInv (rpxLeadingCoeff divisor)))
            (rpxCoeff divisor (rpxDegree divisor)) := by
    have shifted :=
      rpxCoeffMonomialMul (qnfMul (rpxLeadingCoeff dividend) (qnfInv (rpxLeadingCoeff divisor)))
        divisor (rpxDegree divisor) (rpxDegree dividend - rpxDegree divisor)
    rw [natAddSubOfLe isDivisorDegreeLe] at shifted
    exact shifted
  have collapse :
      qnfMul (qnfMul (rpxLeadingCoeff dividend) (qnfInv (rpxLeadingCoeff divisor)))
          (rpxLeadingCoeff divisor)
        = rpxLeadingCoeff dividend :=
    (qnfMulAssoc (rpxLeadingCoeff dividend) (qnfInv (rpxLeadingCoeff divisor))
        (rpxLeadingCoeff divisor)).trans
      ((congrArg (qnfMul (rpxLeadingCoeff dividend)) (qnfInvMulCancels divisorLeadNonzero)).trans
        (qnfMulOneRight (rpxLeadingCoeff dividend)))
  rw [rpxCoeffSub, quotientTermTopCoeff,
    ← rpxLeadingCoeffEqCoeffDegree dividend, ← rpxLeadingCoeffEqCoeffDegree divisor, collapse]
  exact (qnfSubEqAddNeg (rpxLeadingCoeff dividend) (rpxLeadingCoeff dividend)).trans
    (qnfAddNegRight (rpxLeadingCoeff dividend))

/-- **T1 — the division step strictly decreases the trimmed length.**  For a nonzero divisor and a nonzero
dividend with `rpxDegree divisor ≤ rpxDegree dividend`, the replacement dividend `dividend −
(rpxQuotientTerm divisor dividend) · divisor` has trimmed length strictly below `dividend`'s.  Its
coefficients vanish at `rpxDegree dividend` (leading-term cancellation) and above it (the dividend's own
coefficients are gone past the degree, and the quotient-term product vanishes past position `rpxDegree
dividend`), so `rpdTrimLengthLeOfVanishFrom` bounds the trimmed length by `rpxDegree dividend =
(rpxTrim dividend).length − 1`. -/
theorem rpdStepTrimLengthDecreases (divisor dividend : List QnfRat)
    (divisorNonzero : rpxTrim divisor ≠ [])
    (dividendNonzero : rpxTrim dividend ≠ [])
    (degreeFits : rpxDegree divisor ≤ rpxDegree dividend) :
    (rpxTrim (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).length
      < (rpxTrim dividend).length := by
  have hLenDiv : (rpxTrim dividend).length = rpxDegree dividend + 1 :=
    rpxTrimLengthEqDegreeSucc dividend dividendNonzero
  have vanishing : ∀ position : Nat, rpxDegree dividend ≤ position →
      rpxCoeff (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor)) position = qnfZero := by
    intro position hpos
    cases Nat.eq_or_lt_of_le hpos with
    | inl hEq =>
        rw [← hEq]
        exact rpdStepTopCoeffCancels dividend divisor
          (rpxLeadingCoeffNonzeroWhenNonempty divisor divisorNonzero) degreeFits
    | inr hLt =>
        rw [rpxCoeffSub]
        have divVanishes : rpxCoeff dividend position = qnfZero :=
          rpxCoeffZeroFromTrimLength dividend position (by rw [hLenDiv]; exact hLt)
        have mulVanishes :
            rpxCoeff (rpxMul (rpxQuotientTerm divisor dividend) divisor) position = qnfZero := by
          obtain ⟨extra, hExtra⟩ := Nat.le.dest hLt
          have indexEq :
              ((rpxTrim divisor).length + extra) + (rpxDegree dividend - rpxDegree divisor) = position := by
            rw [rpxTrimLengthEqDegreeSucc divisor divisorNonzero]
            calc ((rpxDegree divisor + 1) + extra) + (rpxDegree dividend - rpxDegree divisor)
                = ((rpxDegree divisor + 1) + (rpxDegree dividend - rpxDegree divisor)) + extra := by
                  rw [Nat.add_assoc, Nat.add_comm extra, ← Nat.add_assoc]
              _ = (rpxDegree dividend + 1) + extra := by
                  rw [Nat.add_comm (rpxDegree divisor + 1) (rpxDegree dividend - rpxDegree divisor),
                    ← Nat.add_assoc, rpdNatSubAddCancel degreeFits]
              _ = position := hExtra
          have applied := rpxMonomialMulCoeffVanishesFarAbove
            (qnfMul (rpxLeadingCoeff dividend) (qnfInv (rpxLeadingCoeff divisor))) divisor
            (rpxDegree dividend - rpxDegree divisor) ((rpxTrim divisor).length + extra)
            (Nat.le_add_right (rpxTrim divisor).length extra)
          rw [indexEq] at applied
          exact applied
        rw [divVanishes, mulVanishes]
        exact (qnfSubEqAddNeg qnfZero qnfZero).trans
          ((congrArg (qnfAdd qnfZero) qnfNegZero).trans (qnfAddZeroLeft qnfZero))
  have lengthLe :
      (rpxTrim (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).length
        ≤ rpxDegree dividend :=
    rpdTrimLengthLeOfVanishFrom _ (rpxDegree dividend) vanishing
  rw [hLenDiv]
  exact Nat.lt_succ_of_le lengthLe

/-! ## T2 — fuel adequacy -/

/-- **The step preserves a nil trim.**  If `dividend` trims to the zero polynomial, so does the step's
replacement dividend: the leading coefficient is `qnfZero`, so the quotient-term product vanishes
coefficientwise, and the subtraction leaves the (all-zero) dividend. -/
theorem rpdStepPreservesTrimNil (divisor dividend : List QnfRat)
    (dividendTrimNil : rpxTrim dividend = []) :
    rpxTrim (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor)) = [] := by
  apply rpdTrimNilOfAllCoeffsZero
  intro position
  rw [rpxCoeffSub]
  have divZero : rpxCoeff dividend position = qnfZero :=
    rpdCoeffZeroOfTrimNil dividend position dividendTrimNil
  have leadZero : rpxLeadingCoeff dividend = qnfZero := by
    show rpxLastOrZero (rpxTrim dividend) = qnfZero
    rw [dividendTrimNil]; rfl
  have prodZero :
      rpxCoeff (rpxMul (rpxQuotientTerm divisor dividend) divisor) position = qnfZero := by
    show rpxCoeff (rpxMul (rpxMonomial (qnfMul (rpxLeadingCoeff dividend) (qnfInv (rpxLeadingCoeff divisor)))
          (rpxDegree dividend - rpxDegree divisor)) divisor) position = qnfZero
    rw [leadZero, qnfMulZeroLeft]
    exact rpdCoeffMonomialZeroMulZero (rpxDegree dividend - rpxDegree divisor) divisor position
  rw [divZero, prodZero]
  exact (qnfSubEqAddNeg qnfZero qnfZero).trans
    ((congrArg (qnfAdd qnfZero) qnfNegZero).trans (qnfAddZeroLeft qnfZero))

/-- **T2 — fuel adequacy for the remainder.**  With `(rpxTrim dividend).length ≤ fuel` and a nonzero
divisor, the remainder of `rpxDivMod fuel divisor dividend` either trims to the zero polynomial or has
degree strictly below the divisor's.  Structural on `fuel`: the guard branch stops with a small remainder;
the step branch recurses on a strictly-shorter dividend (T1), the zero-dividend leaf handled by
`rpdStepPreservesTrimNil`. -/
theorem rpdRemainderAdequate :
    ∀ (fuel : Nat) (divisor dividend : List QnfRat),
      rpxTrim divisor ≠ [] →
      (rpxTrim dividend).length ≤ fuel →
      rpxTrim (rpxDivMod fuel divisor dividend).2 = []
        ∨ rpxDegree (rpxDivMod fuel divisor dividend).2 < rpxDegree divisor
  | 0, _, dividend, _, measureLe => by
      have trimNil : rpxTrim dividend = [] := by
        cases hTrim : rpxTrim dividend with
        | nil => rfl
        | cons trimHead trimTail =>
            rw [hTrim] at measureLe
            exact absurd measureLe (Nat.not_succ_le_zero trimTail.length)
      exact Or.inl trimNil
  | fuel + 1, divisor, dividend, divisorNonzero, measureLe => by
      dsimp only [rpxDivMod]
      cases Nat.decLt (rpxDegree dividend) (rpxDegree divisor) with
      | isTrue isLt => exact Or.inr isLt
      | isFalse isNotLt =>
          have degreeFits : rpxDegree divisor ≤ rpxDegree dividend :=
            (Nat.lt_or_ge (rpxDegree dividend) (rpxDegree divisor)).resolve_left isNotLt
          cases hDividendTrim : rpxTrim dividend with
          | nil =>
              have reducedLe :
                  (rpxTrim (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).length ≤ fuel := by
                rw [rpdStepPreservesTrimNil divisor dividend hDividendTrim]
                exact Nat.zero_le fuel
              exact rpdRemainderAdequate fuel divisor
                (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))
                divisorNonzero reducedLe
          | cons trimHead trimTail =>
              have dividendNonzero : rpxTrim dividend ≠ [] := by
                rw [hDividendTrim]; exact List.cons_ne_nil trimHead trimTail
              have decrease :
                  (rpxTrim (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).length
                    < (rpxTrim dividend).length :=
                rpdStepTrimLengthDecreases divisor dividend divisorNonzero dividendNonzero degreeFits
              have reducedLe :
                  (rpxTrim (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))).length ≤ fuel :=
                Nat.le_of_lt_succ (Nat.lt_of_lt_of_le decrease measureLe)
              exact rpdRemainderAdequate fuel divisor
                (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor))
                divisorNonzero reducedLe

/-! ## T3 — the spec completion -/

/-- **T3 — the remainder degree bound at the adequate fuel `length dividend`.**  For a nonzero divisor,
the remainder of `rpxDivMod dividend.length divisor dividend` either trims to the zero polynomial or has
degree strictly below the divisor's degree.  The fuel `dividend.length` is adequate because
`(rpxTrim dividend).length ≤ dividend.length`. -/
theorem rpdDivModRemainderDegree (divisor dividend : List QnfRat)
    (divisorNonzero : rpxTrim divisor ≠ []) :
    rpxTrim (rpxDivMod dividend.length divisor dividend).2 = []
      ∨ rpxDegree (rpxDivMod dividend.length divisor dividend).2 < rpxDegree divisor :=
  rpdRemainderAdequate dividend.length divisor dividend divisorNonzero (rpdTrimLengthLe dividend)

/-! ## The exact (trim-level) single-step reconstruction (the T4 foundation)

The committed reconstruction `rpxDivModReconstructs` is at the EVALUATION level (a ring-homomorphism
identity holding pointwise).  For "gcd divides both" one wants the COEFFICIENT-level identity `dividend =
quotient·divisor + remainder` as polynomials.  The bridge is `rpdTrimEqOfCoeffEq` — trimming is determined
by the coefficient sequence — plus the additive group law `a + (target − a) = target`, which reconstructs
the division step exactly at the trimmed-polynomial level with no distributivity needed (the subtracted
quotient-term product cancels abstractly). -/

/-- **Trimming is determined by the coefficient sequence.**  Polynomials with equal coefficients at every
position have equal trailing-zero normal forms.  Simultaneous induction on both lists: a nil-vs-cons split
forces the cons side's coefficients all zero (`rpdTrimNilOfAllCoeffsZero`); a cons-vs-cons split matches the
heads and recurses on the tails. -/
theorem rpdTrimEqOfCoeffEq :
    ∀ (leftPoly rightPoly : List QnfRat),
      (∀ position : Nat, rpxCoeff leftPoly position = rpxCoeff rightPoly position) →
      rpxTrim leftPoly = rpxTrim rightPoly
  | [], [], _ => rfl
  | [], rightHead :: rightTail, coeffEq =>
      (rpdTrimNilOfAllCoeffsZero (rightHead :: rightTail) (fun position => (coeffEq position).symm)).symm
  | leftHead :: leftTail, [], coeffEq =>
      rpdTrimNilOfAllCoeffsZero (leftHead :: leftTail) coeffEq
  | leftHead :: leftTail, rightHead :: rightTail, coeffEq => by
      have headEq : leftHead = rightHead := coeffEq 0
      have tailTrimEq : rpxTrim leftTail = rpxTrim rightTail :=
        rpdTrimEqOfCoeffEq leftTail rightTail (fun position => coeffEq (position + 1))
      subst headEq
      show (match rpxTrim leftTail with
            | [] => match qnfDecEq leftHead qnfZero with | isTrue _ => [] | isFalse _ => [leftHead]
            | trimHead :: trimTail => leftHead :: trimHead :: trimTail)
        = (match rpxTrim rightTail with
            | [] => match qnfDecEq leftHead qnfZero with | isTrue _ => [] | isFalse _ => [leftHead]
            | trimHead :: trimTail => leftHead :: trimHead :: trimTail)
      rw [tailTrimEq]

/-- The additive group law `summand + (target − summand) = target`. -/
theorem rpdQnfAddSubSelf (summand target : QnfRat) : qnfAdd summand (qnfSub target summand) = target :=
  (congrArg (qnfAdd summand) (qnfSubEqAddNeg target summand)).trans
    ((qnfAddAssoc summand target (qnfNeg summand)).symm.trans
      ((congrArg (qnfAdd · (qnfNeg summand)) (qnfAddComm summand target)).trans
        ((qnfAddAssoc target summand (qnfNeg summand)).trans
          ((congrArg (qnfAdd target) (qnfAddNegRight summand)).trans
            (qnfAddZeroRight target)))))

/-- **The division step reconstructs the dividend exactly (trimmed-polynomial level).**  Adding the
quotient-term product back to the step's replacement dividend recovers the dividend as a polynomial:
`rpxTrim ((quotientTerm · divisor) + (dividend − quotientTerm · divisor)) = rpxTrim dividend`.  This is the
coefficient-level content the eval-only `rpxDivModReconstructs` does not give — proved with no
distributivity, since the subtracted term cancels abstractly (`rpdQnfAddSubSelf`) at every coefficient. -/
theorem rpdStepReconstructsTrim (divisor dividend : List QnfRat) :
    rpxTrim (rpxAdd (rpxMul (rpxQuotientTerm divisor dividend) divisor)
        (rpxSub dividend (rpxMul (rpxQuotientTerm divisor dividend) divisor)))
      = rpxTrim dividend := by
  apply rpdTrimEqOfCoeffEq
  intro position
  rw [rpxCoeffAdd, rpxCoeffSub]
  exact rpdQnfAddSubSelf
    (rpxCoeff (rpxMul (rpxQuotientTerm divisor dividend) divisor) position)
    (rpxCoeff dividend position)

/-! ## Groundings (fires) -/

set_option maxRecDepth 8192

/-- The linear factor `x − 1` = `[-1, 1]` is a nonzero divisor: `rpxTrim [-1, 1] ≠ []`. -/
theorem rpdFireLinearFactorNonzero : rpxTrim [qnfOfInt (-1), qnfOfInt 1] ≠ [] := by
  rw [show rpxTrim [qnfOfInt (-1), qnfOfInt 1] = [qnfOfInt (-1), qnfOfInt 1] from rfl]
  exact List.cons_ne_nil (qnfOfInt (-1)) [qnfOfInt 1]

/-- The dividend `x² − 1` = `[-1, 0, 1]` is nonzero: `rpxTrim [-1, 0, 1] ≠ []`. -/
theorem rpdFireDifferenceOfSquaresNonzero :
    rpxTrim [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] ≠ [] := by
  rw [show rpxTrim [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
        = [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] from rfl]
  exact List.cons_ne_nil (qnfOfInt (-1)) [qnfOfInt 0, qnfOfInt 1]

/-- Fire (the degree conjunct the committed division fire left open): `x² − 1` divided by `x − 1` at the
adequate fuel `length [-1,0,1] = 3` leaves a remainder that trims to the zero polynomial or has degree
below the divisor — here it trims to `[]` (`x − 1` divides `x² − 1` exactly). -/
theorem rpdFireDifferenceOfSquaresRemainderDegree :
    rpxTrim (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).2 = []
      ∨ rpxDegree (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).2
          < rpxDegree [qnfOfInt (-1), qnfOfInt 1] :=
  rpdDivModRemainderDegree [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
    rpdFireLinearFactorNonzero

/-- Fire (nonzero remainder): `x² + 1` divided by `x − 1` at fuel `3` leaves the constant remainder `2`,
which has degree `0 < 1 = rpxDegree (x − 1)` — the right disjunct fires. -/
theorem rpdFireOnePlusSquareRemainderDegree :
    rpxTrim (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]).2 = []
      ∨ rpxDegree (rpxDivMod 3 [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]).2
          < rpxDegree [qnfOfInt (-1), qnfOfInt 1] :=
  rpdDivModRemainderDegree [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt 1, qnfOfInt 0, qnfOfInt 1]
    rpdFireLinearFactorNonzero

/-- Fire (leading-term cancellation, closed value): the step on `x² − 1` by `x − 1` kills the coefficient
at position `2` (the old top degree) — an instance of `rpdStepTopCoeffCancels`. -/
theorem rpdFireStepTopCoeffCancels :
    rpxCoeff
        (rpxSub [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
          (rpxMul (rpxQuotientTerm [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])
            [qnfOfInt (-1), qnfOfInt 1]))
        (rpxDegree [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])
      = qnfZero :=
  rpdStepTopCoeffCancels [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 1]
    (rpxLeadingCoeffNonzeroWhenNonempty [qnfOfInt (-1), qnfOfInt 1] rpdFireLinearFactorNonzero)
    (Nat.le_succ_of_le (Nat.le_refl 1))

/-- Fire (strict trimmed-length decrease, closed value): the step on `x² − 1` by `x − 1` produces a
replacement dividend whose trimmed length (`1`) is strictly below the dividend's (`3`) — an instance of
`rpdStepTrimLengthDecreases`. -/
theorem rpdFireStepTrimLengthDecreases :
    (rpxTrim (rpxSub [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
        (rpxMul (rpxQuotientTerm [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])
          [qnfOfInt (-1), qnfOfInt 1]))).length
      < (rpxTrim [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]).length :=
  rpdStepTrimLengthDecreases [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
    rpdFireLinearFactorNonzero
    rpdFireDifferenceOfSquaresNonzero
    (Nat.le_succ_of_le (Nat.le_refl 1))

/-- Fire (exact step reconstruction, closed value): the first division step of `(x² − 1) ÷ (x − 1)`
reconstructs `x² − 1` exactly at the trimmed level — `x·(x−1) + (x²−1 − x·(x−1))` trims back to `x² − 1`. -/
theorem rpdFireStepReconstructs :
    rpxTrim (rpxAdd
        (rpxMul (rpxQuotientTerm [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])
          [qnfOfInt (-1), qnfOfInt 1])
        (rpxSub [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]
          (rpxMul (rpxQuotientTerm [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1])
            [qnfOfInt (-1), qnfOfInt 1])))
      = rpxTrim [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1] :=
  rpdStepReconstructsTrim [qnfOfInt (-1), qnfOfInt 1] [qnfOfInt (-1), qnfOfInt 0, qnfOfInt 1]

/-! ## Content marker -/

/-- The ℚ[x] Euclidean division remainder degree bound is decided: at the adequate fuel `dividend.length`, the
remainder of a nonzero-divisor division either trims to the zero polynomial or has degree strictly below the
divisor (`rpdDivModRemainderDegree`). The termination lever is the per-step leading-term cancellation
(`rpdStepTopCoeffCancels`) driving a strict trimmed-length decrease (`rpdStepTrimLengthDecreases`) with fuel
adequacy (`rpdRemainderAdequate`). The exact single-step trim-level reconstruction (`rpdStepReconstructsTrim`,
on `rpdTrimEqOfCoeffEq`) is the coefficient-level foundation for "gcd divides both", decided downstream
(`rpeHasGcdDividesBoth`). -/
def rpdHasRemainderDegreeBound : Bool := true

end FX1Poly.ComputerAlgebra
