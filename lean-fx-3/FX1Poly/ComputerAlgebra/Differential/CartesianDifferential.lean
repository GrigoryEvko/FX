import FX1Poly.ComputerAlgebra.Decision.GroebnerRationalEvaluation

/-! # Cartesian differential category: the polynomial model over the rationals

A cartesian differential category (Blute, Cockett, Seely) axiomatises a differential
combinator `D[f] : A × A → B`, the directional derivative linear in its second argument,
on the maps of a cartesian category. Its canonical model is the category of polynomial
maps over a commutative ring. This module realises that model at `QnfRat` on the Gröbner
substrate: a single-output polynomial map in `k` variables is a `GrqPoly` (canonical
descending-sorted coefficient-bearing monomial list, prefix `grq`), its evaluation
homomorphism is `greEvalPoly`, and equality of maps is the canonical word problem
`grqPolyBeq`.

The primitive added here is the formal partial derivative. Differentiating a term by
variable `i` multiplies the coefficient by that variable's exponent and decrements the
exponent by a structural predecessor on a positive exponent (`cdfExpDecrement`, never
`Nat.sub`, whose order lemmas leak `propext`). Additivity in `f` (CD.1) is discharged
coefficient-wise through `grqCoeff` and `grqPolyExtensionality`, with
`cdfDerivCoeffTermInsert` pushing the derivative through the four-way canonical
`grqTermInsert` merge using only coefficient-linearity of the term derivative
(`cdfTermDerivCoeffAddCoeff`) and `qnf` associativity.

Proven content: the polynomial model with the formal derivative `cdfPartialDeriv`,
well-defined by `cdfPartialDerivKeepsCanonical`, and the directional derivative
`cdfDirectionalDeriv`; the equality decision `cdfDecidePolyEqBool` with soundness
`cdfDecidePolyEqSound`; CD.1 additivity in `f` (`cdfPartialDerivAdditive`), CD.3 the
constant and off-diagonal projection rules (`cdfDerivConstant`, `cdfDerivVariableOther`),
CD.4 the pairing rule (`cdfMapDerivConcat`), and CD.6 additivity of `D[f]` in the vector
argument (`cdfDirectionalAddVector`).

Obstructions: CD.5, the chain rule, needs a polynomial-composition homomorphism
`grqCompose` that the substrate lacks; CD.7, second-derivative symmetry, needs an internal
exponent-vector sortedness invariant absent from `GrqPolyCanonical`; free-CDC completeness,
the Blute–Cockett–Seely normal-form theorem identifying CDC morphisms with polynomial maps,
needs the full free term-model with a confluence and termination proof. These are recorded
in `cdfHasFreeCdcCompleteness`.

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Rational coercion and the structural exponent decrement -/

/-- The `Nat`-into-`QnfRat` embedding `value/1`, factored through `qnfOfInt`. -/
def cdfQnfOfNat (value : Nat) : QnfRat :=
  qnfOfInt (Int.ofNat value)

/-- Decrement one variable's exponent inside an exponent vector by a STRUCTURAL
predecessor — the derivative's exponent step, never `Nat.sub`.  A `1` exponent drops
the variable (returns to exponent `0`), keeping the vector well-shaped. -/
def cdfExpDecrement (varIndex : Nat) : GrbExp → GrbExp
  | [] => []
  | head :: rest =>
      cond (Nat.beq head.variableIndex varIndex)
        (match head.exponent with
          | 0 => rest
          | Nat.succ 0 => rest
          | Nat.succ (Nat.succ predPred) =>
              { variableIndex := varIndex, exponent := Nat.succ predPred } :: rest)
        (head :: cdfExpDecrement varIndex rest)

/-! ## The formal partial derivative -/

/-- Formal partial derivative `∂/∂x_varIndex` of a single term: absent variable
(exponent `0`) contributes nothing; a positive exponent `succ pred` multiplies the
coefficient by `succ pred` and decrements the exponent. -/
def cdfTermPartialDeriv (varIndex : Nat) (term : GrqTerm) : GrqPoly :=
  match grbExpLookup term.exponentVector varIndex with
  | 0 => grqZeroPoly
  | Nat.succ pred =>
      grqTermInsert
        (qnfMul (cdfQnfOfNat (Nat.succ pred)) term.coefficient)
        (cdfExpDecrement varIndex term.exponentVector)
        grqZeroPoly

/-- Formal partial derivative `∂/∂x_varIndex` of a polynomial: the sum of the term
derivatives (an insert-fold of `grqAdd`, so canonical without any input hypothesis). -/
def cdfPartialDeriv (varIndex : Nat) : GrqPoly → GrqPoly
  | [] => grqZeroPoly
  | term :: rest =>
      grqAdd (cdfTermPartialDeriv varIndex term) (cdfPartialDeriv varIndex rest)

/-- Well-definedness of the term derivative: the output is a canonical polynomial. -/
theorem cdfTermPartialDerivKeepsCanonical (varIndex : Nat) (term : GrqTerm) :
    GrqPolyCanonical (cdfTermPartialDeriv varIndex term) := by
  unfold cdfTermPartialDeriv
  cases grbExpLookup term.exponentVector varIndex with
  | zero => exact GrqPolyCanonical.nilIsCanonical
  | succ pred =>
      exact grqTermInsertKeepsCanonical _ _ grqZeroPoly GrqPolyCanonical.nilIsCanonical

/-- Well-definedness: the formal derivative preserves canonical form for any input
polynomial — it is an insert-fold of the canonical-preserving `grqAdd`. -/
theorem cdfPartialDerivKeepsCanonical (varIndex : Nat) :
    (poly : GrqPoly) → GrqPolyCanonical (cdfPartialDeriv varIndex poly)
  | [] => GrqPolyCanonical.nilIsCanonical
  | term :: rest =>
      grqAddKeepsCanonical (cdfTermPartialDeriv varIndex term) (cdfPartialDeriv varIndex rest)
        (cdfPartialDerivKeepsCanonical varIndex rest)

/-! ## The directional derivative `D[f](point, vector) = Σᵢ (∂f/∂xᵢ)(point)·vectorᵢ` -/

/-- The directional-derivative sum over the first `count` variables. -/
def cdfDirectionalAux (poly : GrqPoly) (point vector : List QnfRat) : Nat → QnfRat
  | 0 => qnfZero
  | Nat.succ index =>
      qnfAdd (cdfDirectionalAux poly point vector index)
        (qnfMul (greEvalPoly point (cdfPartialDeriv index poly)) (greEnvLookup vector index))

/-- The directional derivative of `poly` at `point` along `vector`, summing the
`numVars` partial contributions — manifestly linear (degree one) in `vector`. -/
def cdfDirectionalDeriv (numVars : Nat) (poly : GrqPoly) (point vector : List QnfRat) :
    QnfRat :=
  cdfDirectionalAux poly point vector numVars

/-! ## The polynomial-map equality decision -/

/-- The canonical polynomial word problem: two polynomial maps are equal iff their
canonical monomial lists are byte-equal. -/
def cdfDecidePolyEqBool (leftPoly rightPoly : GrqPoly) : Bool :=
  grqPolyBeq leftPoly rightPoly

/-- Soundness: the decision accepts only genuinely-equal polynomial maps. -/
theorem cdfDecidePolyEqSound (leftPoly rightPoly : GrqPoly)
    (hAccepts : cdfDecidePolyEqBool leftPoly rightPoly = true) : leftPoly = rightPoly :=
  grqPolyBeqEq leftPoly rightPoly hAccepts

/-! ## Coefficient of the term derivative -/

/-- The closed form of the coefficient contributed by the derivative of one term. -/
def cdfTermDerivCoeffFormula (varIndex : Nat) (coeff : QnfRat) (exponent probe : GrbExp) :
    QnfRat :=
  match grbExpLookup exponent varIndex with
  | 0 => qnfZero
  | Nat.succ pred =>
      cond (grbExpBeq probe (cdfExpDecrement varIndex exponent))
        (qnfMul (cdfQnfOfNat (Nat.succ pred)) coeff) qnfZero

/-- The coefficient scan of the term derivative equals its closed form. -/
theorem cdfTermDerivCoeff (varIndex : Nat) (coeff : QnfRat) (exponent probe : GrbExp) :
    grqCoeff (cdfTermPartialDeriv varIndex { coefficient := coeff, exponentVector := exponent })
        probe =
      cdfTermDerivCoeffFormula varIndex coeff exponent probe := by
  unfold cdfTermPartialDeriv cdfTermDerivCoeffFormula
  cases grbExpLookup exponent varIndex with
  | zero => rfl
  | succ pred =>
      rw [grqCoeffTermInsert grqZeroPoly (qnfMul (cdfQnfOfNat (Nat.succ pred)) coeff)
        (cdfExpDecrement varIndex exponent) probe]
      exact qnfAddZeroRight
        (cond (grbExpBeq probe (cdfExpDecrement varIndex exponent))
          (qnfMul (cdfQnfOfNat (Nat.succ pred)) coeff) qnfZero)

/-- The term-derivative coefficient vanishes at coefficient `0`. -/
theorem cdfTermDerivCoeffZeroCoeff (varIndex : Nat) (exponent probe : GrbExp) :
    cdfTermDerivCoeffFormula varIndex qnfZero exponent probe = qnfZero := by
  unfold cdfTermDerivCoeffFormula
  cases grbExpLookup exponent varIndex with
  | zero => rfl
  | succ pred =>
      dsimp only
      rw [grqQnfMulZeroRight (cdfQnfOfNat (Nat.succ pred))]
      exact grqCondQnfZeroBothArms (grbExpBeq probe (cdfExpDecrement varIndex exponent))

/-- The term-derivative coefficient is additive in the coefficient. -/
theorem cdfTermDerivCoeffAddCoeff (varIndex : Nat) (leftCoeff rightCoeff : QnfRat)
    (exponent probe : GrbExp) :
    cdfTermDerivCoeffFormula varIndex (qnfAdd leftCoeff rightCoeff) exponent probe =
      qnfAdd (cdfTermDerivCoeffFormula varIndex leftCoeff exponent probe)
        (cdfTermDerivCoeffFormula varIndex rightCoeff exponent probe) := by
  unfold cdfTermDerivCoeffFormula
  cases grbExpLookup exponent varIndex with
  | zero => exact (qnfAddZeroLeft qnfZero).symm
  | succ pred =>
      dsimp only
      rw [qnfMulLeftDistrib (cdfQnfOfNat (Nat.succ pred)) leftCoeff rightCoeff]
      cases grbExpBeq probe (cdfExpDecrement varIndex exponent) with
      | true => rfl
      | false => exact (qnfAddZeroLeft qnfZero).symm

/-! ## The coefficient of the polynomial derivative, pushed through `grqTermInsert` -/

/-- The coefficient scan of a polynomial derivative splits at the head term. -/
theorem cdfDerivCoeffCons (varIndex : Nat) (term : GrqTerm) (rest : GrqPoly) (probe : GrbExp) :
    grqCoeff (cdfPartialDeriv varIndex (term :: rest)) probe =
      qnfAdd (grqCoeff (cdfTermPartialDeriv varIndex term) probe)
        (grqCoeff (cdfPartialDeriv varIndex rest) probe) :=
  grqCoeffAdd (cdfTermPartialDeriv varIndex term) (cdfPartialDeriv varIndex rest) probe

/-- The derivative of `grqTermInsert c e P` scans as the derivative of the single term
`c·x^e` plus the derivative of `P`, by casing the four-way canonical merge and pushing
coefficient-linearity through. -/
theorem cdfDerivCoeffTermInsert (varIndex : Nat) :
    (poly : GrqPoly) → (coefficient : QnfRat) → (exponent probe : GrbExp) →
    grqCoeff (cdfPartialDeriv varIndex (grqTermInsert coefficient exponent poly)) probe =
      qnfAdd (grqCoeff (cdfTermPartialDeriv varIndex
          { coefficient := coefficient, exponentVector := exponent }) probe)
        (grqCoeff (cdfPartialDeriv varIndex poly) probe)
  | [], coefficient, exponent, probe => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertNilOnZeroCoefficient coefficient exponent hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero, cdfTermDerivCoeff,
            cdfTermDerivCoeffZeroCoeff]
          exact (qnfAddZeroLeft (grqCoeff (cdfPartialDeriv varIndex []) probe)).symm
      | false =>
          rw [grqTermInsertNilOnNonzeroCoefficient coefficient exponent hZero,
            cdfDerivCoeffCons]
  | head :: rest, coefficient, exponent, probe => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertOnZeroCoefficient coefficient exponent head rest hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero, cdfTermDerivCoeff,
            cdfTermDerivCoeffZeroCoeff]
          exact (qnfAddZeroLeft (grqCoeff (cdfPartialDeriv varIndex (head :: rest)) probe)).symm
      | false =>
          cases hShared : grbExpBeq exponent head.exponentVector with
          | true =>
              have hExp : exponent = head.exponentVector :=
                grbExpBeqEq exponent head.exponentVector hShared
              cases hSum : qnfBeq (qnfAdd coefficient head.coefficient) qnfZero with
              | true =>
                  rw [grqTermInsertOnCollisionCancel coefficient exponent head rest
                      hZero hShared hSum,
                    cdfDerivCoeffCons varIndex head rest probe,
                    cdfTermDerivCoeff varIndex coefficient exponent probe]
                  rw [show (grqCoeff (cdfTermPartialDeriv varIndex head) probe) =
                        cdfTermDerivCoeffFormula varIndex head.coefficient head.exponentVector probe
                      from cdfTermDerivCoeff varIndex head.coefficient head.exponentVector probe]
                  rw [hExp]
                  rw [(qnfAddAssoc
                    (cdfTermDerivCoeffFormula varIndex coefficient head.exponentVector probe)
                    (cdfTermDerivCoeffFormula varIndex head.coefficient head.exponentVector probe)
                    (grqCoeff (cdfPartialDeriv varIndex rest) probe)).symm,
                    (cdfTermDerivCoeffAddCoeff varIndex coefficient head.coefficient
                      head.exponentVector probe).symm,
                    (qnfBeqIffEq (qnfAdd coefficient head.coefficient) qnfZero).mp hSum,
                    cdfTermDerivCoeffZeroCoeff]
                  exact (qnfAddZeroLeft (grqCoeff (cdfPartialDeriv varIndex rest) probe)).symm
              | false =>
                  rw [grqTermInsertOnCollisionMerge coefficient exponent head rest
                      hZero hShared hSum,
                    cdfDerivCoeffCons varIndex
                      { coefficient := qnfAdd coefficient head.coefficient,
                        exponentVector := head.exponentVector } rest probe,
                    cdfDerivCoeffCons varIndex head rest probe,
                    cdfTermDerivCoeff varIndex coefficient exponent probe]
                  rw [show (grqCoeff (cdfTermPartialDeriv varIndex head) probe) =
                        cdfTermDerivCoeffFormula varIndex head.coefficient head.exponentVector probe
                      from cdfTermDerivCoeff varIndex head.coefficient head.exponentVector probe,
                    show (grqCoeff (cdfTermPartialDeriv varIndex
                          { coefficient := qnfAdd coefficient head.coefficient,
                            exponentVector := head.exponentVector }) probe) =
                        cdfTermDerivCoeffFormula varIndex (qnfAdd coefficient head.coefficient)
                          head.exponentVector probe
                      from cdfTermDerivCoeff varIndex (qnfAdd coefficient head.coefficient)
                        head.exponentVector probe]
                  rw [hExp, cdfTermDerivCoeffAddCoeff varIndex coefficient head.coefficient
                    head.exponentVector probe]
                  exact qnfAddAssoc
                    (cdfTermDerivCoeffFormula varIndex coefficient head.exponentVector probe)
                    (cdfTermDerivCoeffFormula varIndex head.coefficient head.exponentVector probe)
                    (grqCoeff (cdfPartialDeriv varIndex rest) probe)
          | false =>
              cases hLess : grbMonoLess head.exponentVector exponent with
              | true =>
                  rw [grqTermInsertOnGreater coefficient exponent head rest hZero hShared hLess,
                    cdfDerivCoeffCons varIndex
                      { coefficient := coefficient, exponentVector := exponent } (head :: rest) probe]
              | false =>
                  rw [grqTermInsertOnSmaller coefficient exponent head rest hZero hShared hLess,
                    cdfDerivCoeffCons varIndex head (grqTermInsert coefficient exponent rest) probe,
                    cdfDerivCoeffTermInsert varIndex rest coefficient exponent probe,
                    cdfDerivCoeffCons varIndex head rest probe]
                  exact grqQnfAddSwapLeft
                    (grqCoeff (cdfTermPartialDeriv varIndex head) probe)
                    (grqCoeff (cdfTermPartialDeriv varIndex
                      { coefficient := coefficient, exponentVector := exponent }) probe)
                    (grqCoeff (cdfPartialDeriv varIndex rest) probe)

/-- The polynomial derivative's coefficient scan is additive through `grqAdd`. -/
theorem cdfDerivCoeffAdd (varIndex : Nat) :
    (leftPoly rightPoly : GrqPoly) → (probe : GrbExp) →
    grqCoeff (cdfPartialDeriv varIndex (grqAdd leftPoly rightPoly)) probe =
      qnfAdd (grqCoeff (cdfPartialDeriv varIndex leftPoly) probe)
        (grqCoeff (cdfPartialDeriv varIndex rightPoly) probe)
  | [], rightPoly, probe =>
      (qnfAddZeroLeft (grqCoeff (cdfPartialDeriv varIndex rightPoly) probe)).symm
  | term :: rest, rightPoly, probe => by
      show grqCoeff (cdfPartialDeriv varIndex
          (grqTermInsert term.coefficient term.exponentVector (grqAdd rest rightPoly))) probe = _
      rw [cdfDerivCoeffTermInsert varIndex (grqAdd rest rightPoly) term.coefficient
          term.exponentVector probe,
        cdfDerivCoeffAdd varIndex rest rightPoly probe,
        cdfDerivCoeffCons varIndex term rest probe]
      exact (qnfAddAssoc (grqCoeff (cdfTermPartialDeriv varIndex term) probe)
        (grqCoeff (cdfPartialDeriv varIndex rest) probe)
        (grqCoeff (cdfPartialDeriv varIndex rightPoly) probe)).symm

/-! ## CD.1: the formal derivative is additive in `f` -/

/-- CD.1: `∂(f + g)/∂xᵢ = ∂f/∂xᵢ + ∂g/∂xᵢ` — additivity of the differential in the first
argument, over the canonical polynomial model. -/
theorem cdfPartialDerivAdditive (varIndex : Nat) (leftPoly rightPoly : GrqPoly) :
    cdfPartialDeriv varIndex (grqAdd leftPoly rightPoly) =
      grqAdd (cdfPartialDeriv varIndex leftPoly) (cdfPartialDeriv varIndex rightPoly) :=
  grqPolyExtensionality (cdfPartialDeriv varIndex (grqAdd leftPoly rightPoly))
    (grqAdd (cdfPartialDeriv varIndex leftPoly) (cdfPartialDeriv varIndex rightPoly))
    (cdfPartialDerivKeepsCanonical varIndex (grqAdd leftPoly rightPoly))
    (grqAddKeepsCanonical (cdfPartialDeriv varIndex leftPoly)
      (cdfPartialDeriv varIndex rightPoly)
      (cdfPartialDerivKeepsCanonical varIndex rightPoly))
    (fun probe => by
      rw [cdfDerivCoeffAdd varIndex leftPoly rightPoly probe,
        grqCoeffAdd (cdfPartialDeriv varIndex leftPoly) (cdfPartialDeriv varIndex rightPoly)
          probe])

/-! ## CD.3: constant rule and off-diagonal projection rule -/

/-- The term derivative of an absent variable is zero. -/
theorem cdfTermPartialDerivAbsent (varIndex : Nat) (term : GrqTerm)
    (hAbsent : grbExpLookup term.exponentVector varIndex = 0) :
    cdfTermPartialDeriv varIndex term = grqZeroPoly := by
  unfold cdfTermPartialDeriv
  rw [hAbsent]

/-- CD.3 (constant rule): the derivative of the constant-one polynomial is zero. -/
theorem cdfDerivConstant (varIndex : Nat) :
    cdfPartialDeriv varIndex grqOnePoly = grqZeroPoly := by
  show grqAdd (cdfTermPartialDeriv varIndex { coefficient := qnfOne, exponentVector := [] })
      (cdfPartialDeriv varIndex []) = grqZeroPoly
  rw [cdfTermPartialDerivAbsent varIndex { coefficient := qnfOne, exponentVector := [] } rfl]
  rfl

/-- CD.3 (projection rule, off-diagonal): `∂x_j/∂x_i = 0` for `i ≠ j`. -/
theorem cdfDerivVariableOther (varIndex otherIndex : Nat)
    (hDistinct : Nat.beq otherIndex varIndex = false) :
    cdfPartialDeriv varIndex (grqVariablePoly otherIndex) = grqZeroPoly := by
  show grqAdd (cdfTermPartialDeriv varIndex
      { coefficient := qnfOne,
        exponentVector := [{ variableIndex := otherIndex, exponent := 1 }] })
      (cdfPartialDeriv varIndex []) = grqZeroPoly
  rw [cdfTermPartialDerivAbsent varIndex
    { coefficient := qnfOne,
      exponentVector := [{ variableIndex := otherIndex, exponent := 1 }] }
    (by
      show cond (Nat.beq otherIndex varIndex) 1 (grbExpLookup [] varIndex) = 0
      rw [hDistinct]
      rfl)]
  rfl

/-! ## CD.4: the pairing rule (derivative of a tuple is the tuple of derivatives) -/

/-- Concatenation of polynomial-map output vectors (the cartesian pairing). -/
def cdfConcat : List GrqPoly → List GrqPoly → List GrqPoly
  | [], rightMaps => rightMaps
  | leftHead :: leftRest, rightMaps => leftHead :: cdfConcat leftRest rightMaps

/-- The derivative of a polynomial-map output vector — the pointwise partial. -/
def cdfMapPartialDeriv (varIndex : Nat) : List GrqPoly → List GrqPoly
  | [] => []
  | poly :: rest => cdfPartialDeriv varIndex poly :: cdfMapPartialDeriv varIndex rest

/-- CD.4 (pairing rule): differentiating a paired map equals pairing the differentiated
maps — `D` acts pointwise, pairing is concatenation. -/
theorem cdfMapDerivConcat (varIndex : Nat) :
    (leftMaps rightMaps : List GrqPoly) →
    cdfMapPartialDeriv varIndex (cdfConcat leftMaps rightMaps) =
      cdfConcat (cdfMapPartialDeriv varIndex leftMaps) (cdfMapPartialDeriv varIndex rightMaps)
  | [], _ => rfl
  | poly :: rest, rightMaps => by
      show cdfPartialDeriv varIndex poly :: cdfMapPartialDeriv varIndex (cdfConcat rest rightMaps) =
        cdfPartialDeriv varIndex poly ::
          cdfConcat (cdfMapPartialDeriv varIndex rest) (cdfMapPartialDeriv varIndex rightMaps)
      rw [cdfMapDerivConcat varIndex rest rightMaps]

/-! ## CD.6: the directional derivative is additive in the vector argument -/

/-- Pointwise vector addition (missing tail entries act as the zero vector). -/
def cdfVecAdd : List QnfRat → List QnfRat → List QnfRat
  | [], rightVector => rightVector
  | leftHead :: leftRest, [] => leftHead :: leftRest
  | leftHead :: leftRest, rightHead :: rightRest =>
      qnfAdd leftHead rightHead :: cdfVecAdd leftRest rightRest

/-- Lookup is a homomorphism through pointwise vector addition. -/
theorem cdfVecLookupAdd :
    (leftVector rightVector : List QnfRat) → (index : Nat) →
    greEnvLookup (cdfVecAdd leftVector rightVector) index =
      qnfAdd (greEnvLookup leftVector index) (greEnvLookup rightVector index)
  | [], rightVector, index => (qnfAddZeroLeft (greEnvLookup rightVector index)).symm
  | _ :: _, [], _ => (qnfAddZeroRight _).symm
  | _ :: _, _ :: _, 0 => rfl
  | _ :: leftRest, _ :: rightRest, Nat.succ index => cdfVecLookupAdd leftRest rightRest index

/-- CD.6: `D[f](point, v + w) = D[f](point, v) + D[f](point, w)` — the differential is
additive in its vector argument. -/
theorem cdfDirectionalAddVector (poly : GrqPoly) (point leftVector rightVector : List QnfRat) :
    (count : Nat) →
    cdfDirectionalAux poly point (cdfVecAdd leftVector rightVector) count =
      qnfAdd (cdfDirectionalAux poly point leftVector count)
        (cdfDirectionalAux poly point rightVector count)
  | 0 => (qnfAddZeroLeft qnfZero).symm
  | Nat.succ index => by
      show qnfAdd (cdfDirectionalAux poly point (cdfVecAdd leftVector rightVector) index)
          (qnfMul (greEvalPoly point (cdfPartialDeriv index poly))
            (greEnvLookup (cdfVecAdd leftVector rightVector) index)) = _
      rw [cdfDirectionalAddVector poly point leftVector rightVector index,
        cdfVecLookupAdd leftVector rightVector index,
        qnfMulLeftDistrib (greEvalPoly point (cdfPartialDeriv index poly))
          (greEnvLookup leftVector index) (greEnvLookup rightVector index)]
      exact grqQnfAddExchange (cdfDirectionalAux poly point leftVector index)
        (cdfDirectionalAux poly point rightVector index)
        (qnfMul (greEvalPoly point (cdfPartialDeriv index poly)) (greEnvLookup leftVector index))
        (qnfMul (greEvalPoly point (cdfPartialDeriv index poly)) (greEnvLookup rightVector index))

/-! ## Ground examples (kernel `rfl`) -/

/-- The polynomial `x₀²`. -/
def cdfXSquared : GrqPoly :=
  [{ coefficient := qnfOne, exponentVector := [{ variableIndex := 0, exponent := 2 }] }]

/-- The polynomial `2·x₀`. -/
def cdfTwoX : GrqPoly :=
  [{ coefficient := qnfOfInt 2, exponentVector := [{ variableIndex := 0, exponent := 1 }] }]

/-- `∂(x₀²)/∂x₀ = 2·x₀`. -/
theorem cdfExampleDerivXSquared :
    cdfDecidePolyEqBool (cdfPartialDeriv 0 cdfXSquared) cdfTwoX = true :=
  rfl

/-- The derivative of a constant is zero. -/
theorem cdfExampleDerivConstant : cdfPartialDeriv 0 grqOnePoly = grqZeroPoly :=
  rfl

/-- The diagonal projection derivative `∂x₀/∂x₀ = 1`. -/
theorem cdfExampleDerivVariableSame :
    cdfDecidePolyEqBool (cdfPartialDeriv 0 (grqVariablePoly 0)) grqOnePoly = true :=
  rfl

/-- Equal polynomial maps decide `true`. -/
theorem cdfExampleDecideEqualTrue : cdfDecidePolyEqBool cdfXSquared cdfXSquared = true :=
  rfl

/-- Distinct polynomial maps decide `false`. -/
theorem cdfExampleDecideDifferentFalse : cdfDecidePolyEqBool cdfXSquared grqOnePoly = false :=
  rfl

/-- The directional derivative of `x₀²` at `3` along `5` is `2·3·5 = 30`. -/
theorem cdfExampleDirectionalXSquared :
    qnfBeq (cdfDirectionalDeriv 1 cdfXSquared [qnfOfInt 3] [qnfOfInt 5]) (qnfOfInt 30) = true :=
  rfl

/-- A concrete instance of CD.7: the mixed second partials of `x₀²·x₁³` agree,
`∂₀∂₁ = ∂₁∂₀`, though the general symmetry is an obstruction. -/
theorem cdfExampleSecondDerivSymmetric :
    cdfDecidePolyEqBool
      (cdfPartialDeriv 0 (cdfPartialDeriv 1
        [{ coefficient := qnfOne,
           exponentVector := [{ variableIndex := 0, exponent := 2 },
             { variableIndex := 1, exponent := 3 }] }]))
      (cdfPartialDeriv 1 (cdfPartialDeriv 0
        [{ coefficient := qnfOne,
           exponentVector := [{ variableIndex := 0, exponent := 2 },
             { variableIndex := 1, exponent := 3 }] }])) = true :=
  rfl

/-! ## Capability markers -/

/-- The polynomial model of a cartesian differential category over `QnfRat`: the canonical
`GrqPoly` with additive structure `grqAdd`, product `grqMul`, and cartesian pairing
`cdfConcat`; the formal partial derivative `cdfPartialDeriv`, well-defined by
`cdfPartialDerivKeepsCanonical`, and the directional derivative `cdfDirectionalDeriv`; the
equality decision `cdfDecidePolyEqBool` with soundness `cdfDecidePolyEqSound`; and the CDC
axioms holding directly on this model — CD.1 additivity in `f` (`cdfPartialDerivAdditive`),
CD.3 the constant and off-diagonal projection rules (`cdfDerivConstant`,
`cdfDerivVariableOther`), CD.4 pairing (`cdfMapDerivConcat`), and CD.6 vector-additivity
(`cdfDirectionalAddVector`). -/
def cdfHasPolynomialCdcModel : Bool := true

/-- The CDC axioms and completeness theorem this model does not establish. CD.5, the chain
rule `D[g ∘ f](a, v) = D[g](f(a), D[f](a, v))`, is gated on a polynomial-composition
homomorphism `grqCompose : GrqPoly → List GrqPoly → GrqPoly` with its evaluation
homomorphism, which the Gröbner substrate lacks — `grqMul` and `grqAdd` are homomorphisms,
composition is not. CD.7, second-derivative symmetry `∂ᵢ∂ⱼ f = ∂ⱼ∂ᵢ f`, needs the single
derivative's exact coefficient formula `grqCoeff (∂p/∂xᵢ) probe = (probeᵢ + 1) · grqCoeff p
(incrementᵢ probe)`, whose increment-and-decrement cancellation fails on malformed exponent
vectors while `GrqPolyCanonical` constrains only inter-term monomial order, not internal
exponent-vector sortedness. Free-CDC completeness, the Blute–Cockett–Seely theorem
identifying the free CDC on a set of objects with the category of polynomial maps up to
canonical form, needs the full free term-model with a confluent, terminating rewriting
system reducing every CDC expression to a unique polynomial normal form. The concrete
instance `cdfExampleSecondDerivSymmetric` confirms CD.7 content on a specific polynomial. -/
def cdfHasFreeCdcCompleteness : Bool := false

end FX1Poly.ComputerAlgebra
