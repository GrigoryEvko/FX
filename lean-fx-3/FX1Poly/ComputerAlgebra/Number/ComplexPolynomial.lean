import FX1Poly.ComputerAlgebra.Number.ComplexReal

/-! # ComplexPolynomial — the ℂ[x] evaluation foundation

Univariate polynomials over `ComplexReal` and the proof that evaluation is a ring
homomorphism, the substrate for the constructive fundamental theorem of algebra
over the Bishop-complex numbers.

This mirrors the ℤ[x] substrate (`IntUnivariatePolynomial`), where evaluation
`polyEval` is a ring homomorphism `ℤ[x] → ℤ` proved by structural induction with
every equation an `Eq` closed by `congrArg`.  The carrier forces one change:
`ComplexReal` sameness is `DenotesSameComplex`, the undecidable product setoid,
never `Eq` on the underlying approximation sequences.  So every homomorphism
equation is stated up to `DenotesSameComplex`, and every rewrite that was
`congrArg`/`Eq.trans` over ℤ becomes a setoid congruence
(`addComplexRespectsDenotesSame` / `mulComplexRespectsDenotesSame`) threaded
through `denotesSameComplexTrans` / `denotesSameComplexSymm`.

## Representation

A univariate complex polynomial is its ascending coefficient list
`[c₀, c₁, …, cₙ]` denoting `c₀ + c₁·x + ⋯ + cₙ·xⁿ`.  Trailing zeros are permitted
(no normalization is forced), so the type is plain `List ComplexReal` and every
operation is structural on the list, the same convention the ℤ[x] substrate uses.

## The ring homomorphism under evaluation

`evalComplexPoly point` is a ring homomorphism `ℂ[x] → ℂ` up to
`DenotesSameComplex`: it commutes with `+` (`evalComplexPolyAdd`), with scalar `·`
(`evalComplexPolyScale`), with unary negation (`evalComplexPolyNeg`), and with `×`
(`evalComplexPolyMul`, the discrete-convolution correctness of `mulComplexPoly`).

## Zero-axiom design

Every operation is structural on the coefficient list; every law is a structural
induction whose arithmetic routes through the `ComplexReal` commutative-ring
witness laws (`addComplexComm`, `addComplexAssoc`, `addComplexZeroLeft/Right`,
`addComplexNegRight`, `mulComplexComm`, `mulComplexAssoc`, `mulComplexOneRight`,
`mulComplexLeftDistrib`) plus the operation congruences.  The auxiliary ring
identities the ℤ proofs took for granted over a decidable ring (`a·0 ~ 0`, right
distributivity, `a·(-b) ~ -(a·b)`, `-(a+b) ~ -a + -b`, the additive middle-four
interchange) are derived here from those witness laws alone; uniqueness of the
additive inverse does the sign work.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`, `decide`, or
`WellFounded.fix`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The polynomial operations (structural on the ascending coefficient list) -/

/-- Horner evaluation of the ascending coefficient list at `point`:
`c₀ + point·(c₁ + point·(c₂ + ⋯))`. -/
def evalComplexPoly (point : ComplexReal) : List ComplexReal → ComplexReal
  | [] => zeroComplex
  | coeff :: restCoeffs => addComplex coeff (mulComplex point (evalComplexPoly point restCoeffs))

/-- Entrywise coefficient sum with tail padding: `(c₀+d₀) + (c₁+d₁)·x + ⋯`, the longer polynomial's
tail carried through unchanged. -/
def addComplexPoly : List ComplexReal → List ComplexReal → List ComplexReal
  | [], rightPoly => rightPoly
  | leftPoly, [] => leftPoly
  | leftHead :: leftTail, rightHead :: rightTail =>
      addComplex leftHead rightHead :: addComplexPoly leftTail rightTail

/-- Scalar multiple: `scalar·c₀ + scalar·c₁·x + ⋯`. -/
def scaleComplexPoly (scalar : ComplexReal) : List ComplexReal → List ComplexReal
  | [] => []
  | coeff :: restCoeffs => mulComplex scalar coeff :: scaleComplexPoly scalar restCoeffs

/-- Coefficientwise negation: `-c₀ + -c₁·x + ⋯`. -/
def negComplexPoly : List ComplexReal → List ComplexReal
  | [] => []
  | coeff :: restCoeffs => negComplex coeff :: negComplexPoly restCoeffs

/-- Polynomial product by convolution: `(c₀ + x·p')·q = c₀·q + x·(p'·q)`, the shift `x·(·)` realized by
a leading `zeroComplex`. -/
def mulComplexPoly : List ComplexReal → List ComplexReal → List ComplexReal
  | [], _ => []
  | leftHead :: leftTail, rightPoly =>
      addComplexPoly (scaleComplexPoly leftHead rightPoly)
        (zeroComplex :: mulComplexPoly leftTail rightPoly)

/-! ## Derived ℂ ring identities (from the commutative-ring witness laws)

The ℤ homomorphism proofs used `intMulZero`, `intRightDistrib`, `intMulNeg`, `intNegAdd`, and the
middle-four `intAddInterchange` freely.  `ComplexReal` provides commutativity, associativity, the
identities, the additive inverse, left distributivity, and the operation congruences — enough to derive
each of these up to `DenotesSameComplex`.  Uniqueness of the additive inverse
(`negComplexUniqueOfAddZero`) supplies the sign identities. -/

/-- The additive middle-four interchange `(a + b) + (c + d) ~ (a + c) + (b + d)` — associativity and
commutativity of complex addition, the ℂ analogue of `intAddInterchange`. -/
theorem addComplexInterchange (valueA valueB valueC valueD : ComplexReal) :
    DenotesSameComplex
      (addComplex (addComplex valueA valueB) (addComplex valueC valueD))
      (addComplex (addComplex valueA valueC) (addComplex valueB valueD)) :=
  denotesSameComplexTrans
    (addComplexAssoc valueA valueB (addComplex valueC valueD))
    (denotesSameComplexTrans
      (addComplexRespectsDenotesSame (denotesSameComplexRefl valueA)
        (denotesSameComplexSymm (addComplexAssoc valueB valueC valueD)))
      (denotesSameComplexTrans
        (addComplexRespectsDenotesSame (denotesSameComplexRefl valueA)
          (addComplexRespectsDenotesSame (addComplexComm valueB valueC)
            (denotesSameComplexRefl valueD)))
        (denotesSameComplexTrans
          (addComplexRespectsDenotesSame (denotesSameComplexRefl valueA)
            (addComplexAssoc valueC valueB valueD))
          (denotesSameComplexSymm
            (addComplexAssoc valueA valueC (addComplex valueB valueD))))))

/-- Negation is a left inverse for complex addition — commutativity carried onto
`addComplexNegRight`. -/
theorem addComplexNegLeft (value : ComplexReal) :
    DenotesSameComplex (addComplex (negComplex value) value) zeroComplex :=
  denotesSameComplexTrans (addComplexComm (negComplex value) value)
    (addComplexNegRight value)

/-- Uniqueness of the additive inverse: if `leftValue + rightValue ~ 0` then
`rightValue ~ -leftValue` — the sign-solving lemma the multiplicative-negation identity rides. -/
theorem negComplexUniqueOfAddZero {leftValue rightValue : ComplexReal}
    (sumIsZero : DenotesSameComplex (addComplex leftValue rightValue) zeroComplex) :
    DenotesSameComplex rightValue (negComplex leftValue) :=
  denotesSameComplexTrans
    (denotesSameComplexSymm (addComplexZeroLeft rightValue))
    (denotesSameComplexTrans
      (addComplexRespectsDenotesSame
        (denotesSameComplexSymm (addComplexNegLeft leftValue))
        (denotesSameComplexRefl rightValue))
      (denotesSameComplexTrans
        (addComplexAssoc (negComplex leftValue) leftValue rightValue)
        (denotesSameComplexTrans
          (addComplexRespectsDenotesSame
            (denotesSameComplexRefl (negComplex leftValue)) sumIsZero)
          (addComplexZeroRight (negComplex leftValue)))))

/-- The product against zero vanishes on the right, `a·0 ~ 0` — `a·0 ~ a·0 + a·0` (left distributivity
on `0 ~ 0 + 0`), then the additive inverse cancels the extra copy. -/
theorem mulComplexZeroRight (factor : ComplexReal) :
    DenotesSameComplex (mulComplex factor zeroComplex) zeroComplex :=
  have productIsSelfSum :
      DenotesSameComplex (mulComplex factor zeroComplex)
        (addComplex (mulComplex factor zeroComplex) (mulComplex factor zeroComplex)) :=
    denotesSameComplexTrans
      (mulComplexRespectsDenotesSame (denotesSameComplexRefl factor)
        (denotesSameComplexSymm (addComplexZeroRight zeroComplex)))
      (mulComplexLeftDistrib factor zeroComplex zeroComplex)
  denotesSameComplexTrans
    (denotesSameComplexSymm (addComplexZeroRight (mulComplex factor zeroComplex)))
    (denotesSameComplexTrans
      (addComplexRespectsDenotesSame (denotesSameComplexRefl (mulComplex factor zeroComplex))
        (denotesSameComplexSymm (addComplexNegRight (mulComplex factor zeroComplex))))
      (denotesSameComplexTrans
        (denotesSameComplexSymm
          (addComplexAssoc (mulComplex factor zeroComplex) (mulComplex factor zeroComplex)
            (negComplex (mulComplex factor zeroComplex))))
        (denotesSameComplexTrans
          (addComplexRespectsDenotesSame (denotesSameComplexSymm productIsSelfSum)
            (denotesSameComplexRefl (negComplex (mulComplex factor zeroComplex))))
          (addComplexNegRight (mulComplex factor zeroComplex)))))

/-- The product against zero vanishes on the left, `0·a ~ 0` — commutativity onto
`mulComplexZeroRight`. -/
theorem mulComplexZeroLeft (factor : ComplexReal) :
    DenotesSameComplex (mulComplex zeroComplex factor) zeroComplex :=
  denotesSameComplexTrans (mulComplexComm zeroComplex factor)
    (mulComplexZeroRight factor)

/-- Right distributivity, `(a + b)·c ~ a·c + b·c` — commutativity onto `mulComplexLeftDistrib`. -/
theorem mulComplexRightDistrib (leftSummand rightSummand factor : ComplexReal) :
    DenotesSameComplex (mulComplex (addComplex leftSummand rightSummand) factor)
      (addComplex (mulComplex leftSummand factor) (mulComplex rightSummand factor)) :=
  denotesSameComplexTrans
    (mulComplexComm (addComplex leftSummand rightSummand) factor)
    (denotesSameComplexTrans
      (mulComplexLeftDistrib factor leftSummand rightSummand)
      (addComplexRespectsDenotesSame
        (mulComplexComm factor leftSummand)
        (mulComplexComm factor rightSummand)))

/-- Negation of zero, `-0 ~ 0` — `-0 ~ 0 + -0` (left identity), then the additive inverse. -/
theorem negComplexZero : DenotesSameComplex (negComplex zeroComplex) zeroComplex :=
  denotesSameComplexTrans
    (denotesSameComplexSymm (addComplexZeroLeft (negComplex zeroComplex)))
    (addComplexNegRight zeroComplex)

/-- Negation distributes over addition, `-(a + b) ~ -a + -b` — componentwise, riding
`negRealAddRealDenotesSame` on each part of the product setoid. -/
theorem negComplexAddComplex (leftValue rightValue : ComplexReal) :
    DenotesSameComplex (negComplex (addComplex leftValue rightValue))
      (addComplex (negComplex leftValue) (negComplex rightValue)) :=
  ⟨negRealAddRealDenotesSame leftValue.realPart rightValue.realPart,
    negRealAddRealDenotesSame leftValue.imaginaryPart rightValue.imaginaryPart⟩

/-- Negation passes through the right factor, `a·(-b) ~ -(a·b)` — `a·b + a·(-b) ~ a·(b + -b) ~ a·0 ~ 0`,
so `a·(-b)` is the additive inverse of `a·b`; uniqueness names it `-(a·b)`. -/
theorem mulComplexNegRight (leftFactor rightFactor : ComplexReal) :
    DenotesSameComplex (mulComplex leftFactor (negComplex rightFactor))
      (negComplex (mulComplex leftFactor rightFactor)) :=
  negComplexUniqueOfAddZero
    (denotesSameComplexTrans
      (denotesSameComplexSymm
        (mulComplexLeftDistrib leftFactor rightFactor (negComplex rightFactor)))
      (denotesSameComplexTrans
        (mulComplexRespectsDenotesSame (denotesSameComplexRefl leftFactor)
          (addComplexNegRight rightFactor))
        (mulComplexZeroRight leftFactor)))

/-! ## Evaluation is a ring homomorphism (by structural induction up to `DenotesSameComplex`) -/

/-- Additivity: `eval(p + q) ~ eval(p) + eval(q)` — induction on both coefficient lists, the Horner
head handled by the middle-four interchange after left distributivity opens `point·(eval p' + eval q')`. -/
theorem evalComplexPolyAdd (point : ComplexReal) :
    ∀ leftPoly rightPoly : List ComplexReal,
      DenotesSameComplex (evalComplexPoly point (addComplexPoly leftPoly rightPoly))
        (addComplex (evalComplexPoly point leftPoly) (evalComplexPoly point rightPoly))
  | [], rightPoly =>
      denotesSameComplexSymm (addComplexZeroLeft (evalComplexPoly point rightPoly))
  | _ :: _, [] =>
      denotesSameComplexSymm (addComplexZeroRight _)
  | leftHead :: leftTail, rightHead :: rightTail =>
      denotesSameComplexTrans
        (addComplexRespectsDenotesSame
          (denotesSameComplexRefl (addComplex leftHead rightHead))
          (mulComplexRespectsDenotesSame (denotesSameComplexRefl point)
            (evalComplexPolyAdd point leftTail rightTail)))
        (denotesSameComplexTrans
          (addComplexRespectsDenotesSame
            (denotesSameComplexRefl (addComplex leftHead rightHead))
            (mulComplexLeftDistrib point (evalComplexPoly point leftTail)
              (evalComplexPoly point rightTail)))
          (addComplexInterchange leftHead rightHead
            (mulComplex point (evalComplexPoly point leftTail))
            (mulComplex point (evalComplexPoly point rightTail))))

/-- Scalar homogeneity: `eval(scalar · p) ~ scalar · eval(p)` — induction on the coefficient list;
the Horner tail `point·(scalar·eval p')` is reassociated to `scalar·(point·eval p')` (assoc + comm) before
folding back through left distributivity. -/
theorem evalComplexPolyScale (point scalar : ComplexReal) :
    ∀ coeffs : List ComplexReal,
      DenotesSameComplex (evalComplexPoly point (scaleComplexPoly scalar coeffs))
        (mulComplex scalar (evalComplexPoly point coeffs))
  | [] => denotesSameComplexSymm (mulComplexZeroRight scalar)
  | coeff :: restCoeffs =>
      denotesSameComplexTrans
        (addComplexRespectsDenotesSame
          (denotesSameComplexRefl (mulComplex scalar coeff))
          (mulComplexRespectsDenotesSame (denotesSameComplexRefl point)
            (evalComplexPolyScale point scalar restCoeffs)))
        (denotesSameComplexTrans
          (addComplexRespectsDenotesSame
            (denotesSameComplexRefl (mulComplex scalar coeff))
            (denotesSameComplexTrans
              (denotesSameComplexSymm
                (mulComplexAssoc point scalar (evalComplexPoly point restCoeffs)))
              (denotesSameComplexTrans
                (mulComplexRespectsDenotesSame (mulComplexComm point scalar)
                  (denotesSameComplexRefl (evalComplexPoly point restCoeffs)))
                (mulComplexAssoc scalar point (evalComplexPoly point restCoeffs)))))
          (denotesSameComplexSymm
            (mulComplexLeftDistrib scalar coeff
              (mulComplex point (evalComplexPoly point restCoeffs)))))

/-- Additive negation: `eval(-p) ~ -eval(p)` — induction on the coefficient list; `mulComplexNegRight`
pushes the negation past the Horner multiplier, `negComplexAddComplex` past the head sum. -/
theorem evalComplexPolyNeg (point : ComplexReal) :
    ∀ coeffs : List ComplexReal,
      DenotesSameComplex (evalComplexPoly point (negComplexPoly coeffs))
        (negComplex (evalComplexPoly point coeffs))
  | [] => denotesSameComplexSymm negComplexZero
  | coeff :: restCoeffs =>
      denotesSameComplexTrans
        (addComplexRespectsDenotesSame (denotesSameComplexRefl (negComplex coeff))
          (mulComplexRespectsDenotesSame (denotesSameComplexRefl point)
            (evalComplexPolyNeg point restCoeffs)))
        (denotesSameComplexTrans
          (addComplexRespectsDenotesSame (denotesSameComplexRefl (negComplex coeff))
            (mulComplexNegRight point (evalComplexPoly point restCoeffs)))
          (denotesSameComplexSymm
            (negComplexAddComplex coeff (mulComplex point (evalComplexPoly point restCoeffs)))))

/-- Multiplicativity: `eval(p × q) ~ eval(p) × eval(q)` — the discrete-convolution correctness of
`mulComplexPoly`, by induction on the left polynomial.  Each head step opens the convolution through
`evalComplexPolyAdd` and `evalComplexPolyScale`, collapses the shift's leading `zeroComplex`, folds the IH
tail with `mulComplexAssoc`, and matches the Horner-expanded product via right distributivity. -/
theorem evalComplexPolyMul (point : ComplexReal) :
    ∀ leftPoly rightPoly : List ComplexReal,
      DenotesSameComplex (evalComplexPoly point (mulComplexPoly leftPoly rightPoly))
        (mulComplex (evalComplexPoly point leftPoly) (evalComplexPoly point rightPoly))
  | [], rightPoly =>
      denotesSameComplexSymm (mulComplexZeroLeft (evalComplexPoly point rightPoly))
  | leftHead :: leftTail, rightPoly =>
      have tailSimplifies :
          DenotesSameComplex
            (evalComplexPoly point (zeroComplex :: mulComplexPoly leftTail rightPoly))
            (mulComplex point
              (mulComplex (evalComplexPoly point leftTail) (evalComplexPoly point rightPoly))) :=
        denotesSameComplexTrans
          (addComplexRespectsDenotesSame (denotesSameComplexRefl zeroComplex)
            (mulComplexRespectsDenotesSame (denotesSameComplexRefl point)
              (evalComplexPolyMul point leftTail rightPoly)))
          (addComplexZeroLeft
            (mulComplex point
              (mulComplex (evalComplexPoly point leftTail) (evalComplexPoly point rightPoly))))
      have distributeRight :
          DenotesSameComplex
            (mulComplex
              (addComplex leftHead (mulComplex point (evalComplexPoly point leftTail)))
              (evalComplexPoly point rightPoly))
            (addComplex (mulComplex leftHead (evalComplexPoly point rightPoly))
              (mulComplex point
                (mulComplex (evalComplexPoly point leftTail) (evalComplexPoly point rightPoly)))) :=
        denotesSameComplexTrans
          (mulComplexRightDistrib leftHead (mulComplex point (evalComplexPoly point leftTail))
            (evalComplexPoly point rightPoly))
          (addComplexRespectsDenotesSame
            (denotesSameComplexRefl (mulComplex leftHead (evalComplexPoly point rightPoly)))
            (mulComplexAssoc point (evalComplexPoly point leftTail)
              (evalComplexPoly point rightPoly)))
      denotesSameComplexTrans
        (evalComplexPolyAdd point (scaleComplexPoly leftHead rightPoly)
          (zeroComplex :: mulComplexPoly leftTail rightPoly))
        (denotesSameComplexTrans
          (addComplexRespectsDenotesSame (evalComplexPolyScale point leftHead rightPoly)
            (denotesSameComplexRefl
              (evalComplexPoly point (zeroComplex :: mulComplexPoly leftTail rightPoly))))
          (denotesSameComplexTrans
            (addComplexRespectsDenotesSame
              (denotesSameComplexRefl (mulComplex leftHead (evalComplexPoly point rightPoly)))
              tailSimplifies)
            (denotesSameComplexSymm distributeRight)))

/-- Content marker: the ℂ[x] substrate carries evaluation proved to be a ring homomorphism up to the
product setoid — additive (`evalComplexPolyAdd`), scalar-homogeneous (`evalComplexPolyScale`),
negation-commuting (`evalComplexPolyNeg`), and multiplicative (`evalComplexPolyMul`, the convolution
correctness) — over the Bishop-complex numbers, with every derived sign and distributivity identity built
from the ℂ commutative-ring witness laws alone.  This is the foundation for the constructive fundamental
theorem of algebra. -/
def fxComplexReal_hasPolynomialEvaluation : Bool := true

end FX1Poly.ComputerAlgebra
