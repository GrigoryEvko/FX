import FX1Poly.ComputerAlgebra.Decision.GroebnerRationalEvaluation

/-! # FX1Poly/ComputerAlgebra/Differential/CartesianDifferential — the polynomial
    model of a cartesian differential category (Blute–Cockett–Seely axioms over ℚ)

A cartesian differential category (CDC) axiomatises the differential combinator
`D[f] : A × A → B` ("directional derivative", linear in the second argument) that a
polynomial map carries.  The canonical model is the category of polynomial maps over a
commutative ring: this module instantiates it at `QnfRat` reusing the shipped Gröbner
substrate verbatim — a polynomial map (single output, `k` inputs) is a `GrqPoly`
(canonical descending-sorted coefficient-carrying monomial list, prefix `grq`), its
evaluation homomorphism is `greEvalPoly`, and its equality decision is the canonical
`grqPolyBeq` word problem.

The ONE new primitive is the formal partial derivative `∂/∂xᵢ`: term-wise the
coefficient is multiplied by the variable's exponent and that exponent is decremented
by a STRUCTURAL predecessor on a positive exponent (`cdfExpDecrement`, never `Nat.sub`
whose order lemmas leak `propext`).  Additivity in `f` (CD.1) is discharged
coefficient-wise through `grqCoeff`/`grqPolyExtensionality`; the load-bearing lemma
`cdfDerivCoeffTermInsert` pushes the derivative through the four-way canonical
`grqTermInsert` merge using nothing but coefficient-linearity of the term derivative
(`cdfTermDerivCoeffAddCoeff`) and `qnf` associativity — robust to malformed probes.

## What lands (DECIDED, zero-axiom)

  * **T1** the polynomial model (reused) + the formal derivative `cdfPartialDeriv` with
    well-definedness `cdfPartialDerivKeepsCanonical`; the directional derivative
    `cdfDirectionalDeriv` = `Σᵢ (∂f/∂xᵢ)(point) · vectorᵢ`.
  * **T2** the decision `cdfDecidePolyEqBool` with soundness `cdfDecidePolyEqSound`.
  * **T3** CD.1 additivity in `f` (`cdfPartialDerivAdditive`); CD.3 the constant rule
    (`cdfDerivConstant`) and the off-diagonal projection rule (`cdfDerivVariableOther`);
    CD.4 the pairing rule (`cdfMapDerivConcat`, derivative of a tuple = tuple of
    derivatives); CD.6 additivity of `D[f]` in the vector argument
    (`cdfDirectionalAddVector`).

## The walls (owner `false`, honest obstructions)

  * **CD.5 chain rule** (`cdfHasChainRule`) — needs a polynomial-composition /
    substitution homomorphism `grqCompose` over `GrqPoly` that does not exist in the
    substrate; two attacks burn on that missing primitive.
  * **CD.7 second-derivative symmetry** (`cdfHasSecondDerivSymmetry`) — the single
    derivative's exact coefficient formula needs an internal exponent-vector
    sortedness invariant that `GrqPolyCanonical` does not carry.
  * **T4 free-CDC completeness** (`cdfHasFreeCdcCompleteness`) — the Blute–Cockett–Seely
    normal-form theorem identifying CDC terms with polynomial maps needs the full free
    term-model / confluence construction; no kernel-checked artifact exists.

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Prelude: the natural-number-into-ℚ coercion and the structural exponent drop -/

/-- The canonical `Nat → QnfRat` embedding: `value/1` via the shipped ℤ embedding. -/
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

/-! ## T1: the formal partial derivative -/

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

/-- **T1 well-definedness**: the formal derivative preserves canonical form for ANY
input polynomial — it is an insert-fold of the canonical-preserving `grqAdd`. -/
theorem cdfPartialDerivKeepsCanonical (varIndex : Nat) :
    (poly : GrqPoly) → GrqPolyCanonical (cdfPartialDeriv varIndex poly)
  | [] => GrqPolyCanonical.nilIsCanonical
  | term :: rest =>
      grqAddKeepsCanonical (cdfTermPartialDeriv varIndex term) (cdfPartialDeriv varIndex rest)
        (cdfPartialDerivKeepsCanonical varIndex rest)

/-! ## T1: the directional derivative `D[f](point, vector) = Σᵢ (∂f/∂xᵢ)(point)·vectorᵢ` -/

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

/-! ## T2: the polynomial-map equality decision -/

/-- The canonical polynomial word problem: two polynomial maps are equal iff their
canonical monomial lists are byte-equal. -/
def cdfDecidePolyEqBool (leftPoly rightPoly : GrqPoly) : Bool :=
  grqPolyBeq leftPoly rightPoly

/-- **T2 soundness**: the decision accepts only genuinely-equal polynomial maps. -/
theorem cdfDecidePolyEqSound (leftPoly rightPoly : GrqPoly)
    (hAccepts : cdfDecidePolyEqBool leftPoly rightPoly = true) : leftPoly = rightPoly :=
  grqPolyBeqEq leftPoly rightPoly hAccepts

/-! ## Coefficient characterisation of the term derivative (the CD.1 engine) -/

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

/-- The term-derivative coefficient is additive in the coefficient — the linearity the
collision-merge branch of `grqTermInsert` consumes. -/
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

/-- **The CD.1 engine**: the derivative of `grqTermInsert c e P` scans as the derivative
of the single term `c·x^e` plus the derivative of `P` — proven by casing the four-way
canonical merge and pushing linearity through, robust to any probe. -/
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

/-! ## T3 CD.1: the formal derivative is additive in `f` -/

/-- **CD.1**: `∂(f + g)/∂xᵢ = ∂f/∂xᵢ + ∂g/∂xᵢ` — additivity of the differential in the
first argument, over the canonical polynomial model. -/
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

/-! ## T3 CD.3: constant rule and off-diagonal projection rule -/

/-- The term derivative of an absent variable is zero. -/
theorem cdfTermPartialDerivAbsent (varIndex : Nat) (term : GrqTerm)
    (hAbsent : grbExpLookup term.exponentVector varIndex = 0) :
    cdfTermPartialDeriv varIndex term = grqZeroPoly := by
  unfold cdfTermPartialDeriv
  rw [hAbsent]

/-- **CD.3 (constant rule)**: the derivative of the constant-one polynomial is zero. -/
theorem cdfDerivConstant (varIndex : Nat) :
    cdfPartialDeriv varIndex grqOnePoly = grqZeroPoly := by
  show grqAdd (cdfTermPartialDeriv varIndex { coefficient := qnfOne, exponentVector := [] })
      (cdfPartialDeriv varIndex []) = grqZeroPoly
  rw [cdfTermPartialDerivAbsent varIndex { coefficient := qnfOne, exponentVector := [] } rfl]
  rfl

/-- **CD.3 (projection rule, off-diagonal)**: `∂x_j/∂x_i = 0` for `i ≠ j`. -/
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

/-! ## T3 CD.4: the pairing rule (derivative of a tuple is the tuple of derivatives) -/

/-- Concatenation of polynomial-map output vectors (the cartesian pairing). -/
def cdfConcat : List GrqPoly → List GrqPoly → List GrqPoly
  | [], rightMaps => rightMaps
  | leftHead :: leftRest, rightMaps => leftHead :: cdfConcat leftRest rightMaps

/-- The derivative of a polynomial-map output vector — the pointwise partial. -/
def cdfMapPartialDeriv (varIndex : Nat) : List GrqPoly → List GrqPoly
  | [] => []
  | poly :: rest => cdfPartialDeriv varIndex poly :: cdfMapPartialDeriv varIndex rest

/-- **CD.4 (pairing rule)**: differentiating a paired map equals pairing the
differentiated maps — `D` acts pointwise, pairing is concatenation. -/
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

/-! ## T3 CD.6: the directional derivative is additive in the vector argument -/

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

/-- **CD.6**: `D[f](point, v + w) = D[f](point, v) + D[f](point, w)` — the differential
is additive in its vector argument. -/
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

/-! ## T5: ground kernel-`rfl` fires -/

/-- The polynomial `x₀²`. -/
def cdfXSquared : GrqPoly :=
  [{ coefficient := qnfOne, exponentVector := [{ variableIndex := 0, exponent := 2 }] }]

/-- The polynomial `2·x₀`. -/
def cdfTwoX : GrqPoly :=
  [{ coefficient := qnfOfInt 2, exponentVector := [{ variableIndex := 0, exponent := 1 }] }]

/-- Fire: `∂(x₀²)/∂x₀ = 2·x₀`. -/
theorem cdfFireDerivXSquared : cdfDecidePolyEqBool (cdfPartialDeriv 0 cdfXSquared) cdfTwoX = true :=
  rfl

/-- Fire: the derivative of a constant is zero. -/
theorem cdfFireDerivConstant : cdfPartialDeriv 0 grqOnePoly = grqZeroPoly :=
  rfl

/-- Fire: the diagonal projection derivative `∂x₀/∂x₀ = 1`. -/
theorem cdfFireDerivVariableSame :
    cdfDecidePolyEqBool (cdfPartialDeriv 0 (grqVariablePoly 0)) grqOnePoly = true :=
  rfl

/-- Fire: equal polynomial maps decide `true`. -/
theorem cdfFireDecideEqualTrue : cdfDecidePolyEqBool cdfXSquared cdfXSquared = true :=
  rfl

/-- Fire: distinct polynomial maps decide `false`. -/
theorem cdfFireDecideDifferentFalse : cdfDecidePolyEqBool cdfXSquared grqOnePoly = false :=
  rfl

/-- Fire: the directional derivative of `x₀²` at `3` along `5` is `2·3·5 = 30`. -/
theorem cdfFireDirectionalXSquared :
    qnfBeq (cdfDirectionalDeriv 1 cdfXSquared [qnfOfInt 3] [qnfOfInt 5]) (qnfOfInt 30) = true :=
  rfl

/-- Fire (CD.7 evidence): the mixed second partials of `x₀²·x₁³` agree
(`∂₀∂₁ = ∂₁∂₀`) at a concrete polynomial, though the general symmetry is walled. -/
theorem cdfFireSecondDerivSymmetric :
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

/-! ## Content markers: DECIDED landings and the honest walls -/

/-- DECIDED: the polynomial model of the CDC is the reused canonical `GrqPoly` over
`QnfRat`, with additive structure `grqAdd`, product `grqMul`, and pairing `cdfConcat`. -/
def cdfHasPolynomialModel : Bool := true

/-- DECIDED: the formal partial derivative `cdfPartialDeriv` with structural-predecessor
exponent decrement, well-defined by `cdfPartialDerivKeepsCanonical`, and the directional
derivative `cdfDirectionalDeriv`. -/
def cdfHasFormalDerivative : Bool := true

/-- DECIDED: the polynomial-map equality decision `cdfDecidePolyEqBool` with soundness
`cdfDecidePolyEqSound` (the canonical word problem). -/
def cdfHasEqualityDecision : Bool := true

/-- DECIDED: the easy CDC axioms over the polynomial model — CD.1 additivity in `f`
(`cdfPartialDerivAdditive`), CD.3 constant / off-diagonal-projection rules
(`cdfDerivConstant` / `cdfDerivVariableOther`), CD.4 pairing (`cdfMapDerivConcat`), and
CD.6 vector-additivity of the differential (`cdfDirectionalAddVector`). -/
def cdfHasEasyAxioms : Bool := true

/-- WALL (CD.5 chain rule): `D[g ∘ f](a, v) = D[g](f(a), D[f](a, v))` is NOT proven.
Obstruction: it is gated on a polynomial-composition / substitution homomorphism
`grqCompose : GrqPoly → List GrqPoly → GrqPoly` (substitute one polynomial per variable)
together with its evaluation homomorphism, and NO such operation exists in the Gröbner
substrate — `grqMul` / `grqAdd` are homomorphisms but composition is not.  Two attacks
burned: (1) direct — the multivariate chain rule as a coefficient identity relating
`cdfPartialDeriv i (grqCompose g f)` to the Jacobian product needs `grqCompose` first;
(2) semantic via `greEvalMul` — evaluation is multiplicative but a directional
chain-rule cross-check still requires composing the polynomial maps, i.e. `grqCompose`.
Both burn on the missing composition primitive. -/
def cdfHasChainRule : Bool := false

/-- WALL (CD.7 second-derivative symmetry): `∂ᵢ∂ⱼ f = ∂ⱼ∂ᵢ f` in general is NOT proven.
Obstruction: the clean route is the single derivative's exact coefficient formula
`grqCoeff (∂p/∂xᵢ) probe = (probeᵢ + 1) · grqCoeff p (incrementᵢ probe)`, but the
increment/decrement cancellation lemmas (`lookup (increment i e) i = succ (lookup e i)`,
`decrement i (increment i e) = e`) FAIL on malformed exponent vectors (a zero exponent
or a duplicated / unsorted variable), and `GrqPolyCanonical` constrains only the
inter-term monomial ORDER, NOT internal exponent-vector sortedness — so extensionality
over ALL probes has no well-formedness to lean on.  Two attacks burned: (1) the
coefficient formula, dead on the missing sortedness invariant; (2) a direct
double-induction on term structure, dead because the two derivative orders reorder terms
through independent `grqAdd` folds with no shared canonical pivot and the diagonal
double-decrement coefficient `(k+2)(k+1)` re-sort has no commutation lemma.  (The
concrete instance `cdfFireSecondDerivSymmetric` fires, confirming the content.) -/
def cdfHasSecondDerivSymmetry : Bool := false

/-- WALL (T4 free-CDC completeness): the Blute–Cockett–Seely theorem "the free cartesian
differential category on a set of objects IS the category of polynomial maps, and two
morphisms are equal iff their canonical polynomial forms coincide" is NOT proven.  The
soundness direction (polynomial maps model the CDC axioms) is the landed content above;
the faithfulness / completeness direction needs the full free term-model construction —
a rewriting system on CDC expressions with a confluence + termination proof reducing
every term to a unique polynomial normal form (the 2-category word-problem flavour) —
and no kernel-checked free-CDC normal-form artifact exists anywhere. -/
def cdfHasFreeCdcCompleteness : Bool := false

end FX1Poly.ComputerAlgebra
