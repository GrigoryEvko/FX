import FX1Poly.ComputerAlgebra.Decision.GroebnerMembership
import FX1Poly.ComputerAlgebra.Number.NormalizedRational

/-! # FX1Poly/ComputerAlgebra/Decision/GroebnerRationalMembership — the DISSAT-GROB
    certificate route over ℚ (ideal membership by checkable cofactor certificates,
    canonical-normal-form rational coefficients)

The F2 brick (`GroebnerMembership.lean`, prefix `grb`) shipped the reflection split —
untrusted fuel-bounded finder with cofactor accumulation, certified checker
`p = Σ qᵢ·gᵢ`, semantic inductive, soundness on the checker only — at Bool
coefficients, because ℚ had no canonical normal form and structural beq on sorted
coefficient lists would have been equality-up-to-setoid everywhere.  That
prerequisite landed as `NormalizedRational.lean` (prefix `qnf`): `QnfRat` with
byte-equality = rational equality, plain-`Eq` field laws, structural `qnfBeq` with
`qnfBeqIffEq`, and `qnfInv` + `qnfMulInvCancels` on a plain disequality.  This module
is the SAME certificate architecture instantiated at `QnfRat`.

## Architecture decision: (B) monomorphic clone, consciously

Two shapes were on the table: (A) a shared core parameterized over a
coefficient-field bundle, instantiated at Bool and `QnfRat`; (B) a concrete
monomorphic clone at `QnfRat`.  This module is (B): polymorphic `Eq` manipulation is
a known propext source in this repo (match-compiler splitter auxes over a type
variable pull `propext`; the zero-axiom recipes are all per-carrier), the repo norm
is per-carrier monomorphic kits (the whole `qnf`/`Int`/`Nat` number tower), and the
F2 brick stays untouched as the commissioned reference.  The price — structural
duplication of the order/insert/scan scaffolding — is paid once and audited per
declaration.

## What ℚ changes against F2, layer by layer

  * **Terms** (`GrqTerm`) — a monomial now CARRIES a coefficient
    (`coefficient : QnfRat`, `exponentVector : GrbExp`); the F2 collapse
    "stored monomial = coefficient 1" is gone.  The exponent-vector substrate —
    `GrbExp`, `grbExpMul`, the graded-lex `grbMonoLess` with its four hand-proved
    order laws, `grbExpDivides` / `grbExpQuotient` — is REUSED from the F2 brick by
    import, untouched.
  * **Canonical form** (`GrqPolyCanonical`) — strictly-descending exponent vectors
    AND every stored coefficient nonzero (`qnfBeq coefficient qnfZero = false`).
    Zero-coefficient stripping is decidable EXACTLY because the coefficient carrier
    is canonical: `qnfBeq · qnfZero` is rational equality with zero.
  * **Insert** (`grqTermInsert`) — four-way: zero-coefficient guard (identity),
    collision with coefficient ADDITION (drop the pair when the sum vanishes, merge
    otherwise), and the two F2 order branches.  `grqAdd left right` is canonical
    whenever `right` is, for ANY left operand — the F2 trick that makes `grqMul` and
    `grqSumOfProducts` unconditionally canonical with no well-formedness threading.
  * **The workhorse** (`grqPolyExtensionality`) — canonical lists with
    pointwise-equal `QnfRat` coefficient scans (`grqCoeff`) are byte-equal.  With
    canonical coefficients this is STRUCTURALLY TRUE: the scan of a canonical list
    at its own head exponent IS the head coefficient (`grqCoeffHeadIsCoefficient`),
    and a nonzero scan in a tail forces strict domination
    (`grqCoeffNonzeroImpliesLessThanHead`).
  * **The AC family** — one-fire extensionality over hand-telescoped `qnf` law
    chains (`qnfAddAssoc`/`qnfAddComm`/`qnfAddNegRight`/... — NEVER re-proved, only
    composed; the handful of derived group/ring consequences the scans need —
    swap-left, exchange, inverse uniqueness, `-(a+b) = -a + -b`, `c·0 = 0`,
    `(-c)·a = -(c·a)` — are telescoped here as `grqQnf*`).
  * **THE CHECKER** (`grqCheckCertificate`) — structural `grqPolyBeq` of
    `grqSumOfProducts cofactors generators` against the target; soundness
    (`grqCertificateSound`) lands in the semantic inductive `GrqInIdeal` and needs
    NO canonicity on any input.
  * **THE FINDER** (`grqReduce`) — fuel-bounded top-reduction.  THE STEP F2 GOT FOR
    FREE: the reducer scale is `leadCoefficient · qnfInv(generatorLeadCoefficient)`
    — division by an arbitrary nonzero rational via `qnfInv` +
    `qnfMulInvCancels`, impossible over ℤ and setoid-poisoned over raw pairs.  THE
    REDUCE INVARIANT (`grqReduceInvariant`): at every fuel level
    `remainder + Σ cofᵢ·genᵢ = input + Σ cof⁰ᵢ·genᵢ` as canonical lists, so finder
    success is self-certifying (`grqFoundCertificateCertifies`).  Reducer-choice
    CORRECTNESS (that the scale actually cancels the lead) is never needed by any
    theorem — it only affects finder progress, witnessed by the kernel-`rfl` fires.
  * **The ℚ-vs-ℤ separator fire** — `2x ∈ ⟨3x⟩` with cofactor `2/3`
    (`grqFireCheckerAcceptsRationalCofactor`, finder emits it in
    `grqFireFinderEmitsRationalCofactor`): no ℤ cofactor exists (`3q = 2` has no
    integer solution), the exact content a rational coefficient field adds.

## The honest wall (cited, not re-minted)

Full NON-membership decision is out of scope exactly as in the F2 brick: see
`grbNonMembershipDecisionStatement` with owner
`fxDissatGrob_hasNonMembershipDecision := false` in `GroebnerMembership.lean` —
walled at Buchberger termination (Dickson, certified zero-axiom-impossible at
`fxNet4_dicksonWall`) plus Newman confluence.  The same two legs block the ℚ case;
no new wall `Prop` is minted here.  The F2 brick's evaluation-homomorphism layer
(`grbEvalPoly` common-zero grounding) is intentionally NOT cloned in this first
landing — the semantic content here is `GrqInIdeal` + `grqCertificateSound`; the
ℚ evaluation layer is the natural successor brick.

## Zero-axiom discipline

Init + the two imported bricks only.  Structural recursion throughout (fuel for the
finder).  No `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`funext`, `omega`, no `WellFounded.fix`, no `decide` on `Prop`, no catch-all arms
over split scrutinees.  All coefficient reasoning is plain `Eq` over `QnfRat`
composed from the `qnf` law kit by `congrArg`/`Eq.trans` telescopes.  Per-declaration
gate in `FX1PolyAudit/ComputerAlgebra/Decision/GroebnerRationalMembership.lean`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Derived QnfRat laws (telescoped from the qnf kit — nothing re-proved) -/

/-- A `cond` whose arms are both the canonical zero is the canonical zero. -/
theorem grqCondQnfZeroBothArms : (flag : Bool) → cond flag qnfZero qnfZero = qnfZero
  | false => rfl
  | true => rfl

/-- Left-swap for canonical addition: `a + (b + c) = b + (a + c)`. -/
theorem grqQnfAddSwapLeft (firstValue secondValue thirdValue : QnfRat) :
    qnfAdd firstValue (qnfAdd secondValue thirdValue) =
      qnfAdd secondValue (qnfAdd firstValue thirdValue) :=
  ((qnfAddAssoc firstValue secondValue thirdValue).symm.trans
      (congrArg (fun value => qnfAdd value thirdValue)
        (qnfAddComm firstValue secondValue))).trans
    (qnfAddAssoc secondValue firstValue thirdValue)

/-- The four-summand exchange: `(a + b) + (c + d) = (a + c) + (b + d)`. -/
theorem grqQnfAddExchange (firstValue secondValue thirdValue fourthValue : QnfRat) :
    qnfAdd (qnfAdd firstValue secondValue) (qnfAdd thirdValue fourthValue) =
      qnfAdd (qnfAdd firstValue thirdValue) (qnfAdd secondValue fourthValue) :=
  (qnfAddAssoc firstValue secondValue (qnfAdd thirdValue fourthValue)).trans
    ((congrArg (qnfAdd firstValue)
        (grqQnfAddSwapLeft secondValue thirdValue fourthValue)).trans
      (qnfAddAssoc firstValue thirdValue (qnfAdd secondValue fourthValue)).symm)

/-- Inverse uniqueness, left form: a vanishing sum pins the left summand to the
negation of the right. -/
theorem grqQnfEqNegOfAddEqZero {leftValue rightValue : QnfRat}
    (sumIsZero : qnfAdd leftValue rightValue = qnfZero) :
    leftValue = qnfNeg rightValue :=
  ((((qnfAddZeroRight leftValue).symm.trans
        (congrArg (qnfAdd leftValue) (qnfAddNegRight rightValue).symm)).trans
      (qnfAddAssoc leftValue rightValue (qnfNeg rightValue)).symm).trans
    (congrArg (fun value => qnfAdd value (qnfNeg rightValue)) sumIsZero)).trans
    (qnfAddZeroLeft (qnfNeg rightValue))

/-- Inverse uniqueness, right form: a vanishing sum pins the negation of the left
summand to the right. -/
theorem grqQnfNegEqOfAddEqZero {leftValue rightValue : QnfRat}
    (sumIsZero : qnfAdd leftValue rightValue = qnfZero) :
    qnfNeg leftValue = rightValue :=
  ((((qnfAddZeroRight (qnfNeg leftValue)).symm.trans
        (congrArg (qnfAdd (qnfNeg leftValue)) sumIsZero.symm)).trans
      (qnfAddAssoc (qnfNeg leftValue) leftValue rightValue).symm).trans
    (congrArg (fun value => qnfAdd value rightValue) (qnfAddNegLeft leftValue))).trans
    (qnfAddZeroLeft rightValue)

/-- Negating the canonical zero gives the canonical zero. -/
theorem grqQnfNegZeroIsZero : qnfNeg qnfZero = qnfZero :=
  (qnfAddZeroLeft (qnfNeg qnfZero)).symm.trans (qnfAddNegRight qnfZero)

/-- Negation distributes over canonical addition. -/
theorem grqQnfNegAddDistrib (leftValue rightValue : QnfRat) :
    qnfNeg (qnfAdd leftValue rightValue) =
      qnfAdd (qnfNeg leftValue) (qnfNeg rightValue) :=
  grqQnfNegEqOfAddEqZero
    ((grqQnfAddExchange leftValue rightValue (qnfNeg leftValue) (qnfNeg rightValue)).trans
      (((congrArg (fun value => qnfAdd value (qnfAdd rightValue (qnfNeg rightValue)))
            (qnfAddNegRight leftValue)).trans
          (qnfAddZeroLeft (qnfAdd rightValue (qnfNeg rightValue)))).trans
        (qnfAddNegRight rightValue)))

/-- Negation pushes into a zero-defaulted `cond` — the coefficient-scan shape. -/
theorem grqQnfNegCondZero : (flag : Bool) → (value : QnfRat) →
    qnfNeg (cond flag value qnfZero) = cond flag (qnfNeg value) qnfZero
  | false, _ => grqQnfNegZeroIsZero
  | true, _ => rfl

/-- Multiplying the canonical zero on the right annihilates. -/
theorem grqQnfMulZeroRight (factor : QnfRat) : qnfMul factor qnfZero = qnfZero :=
  ((((qnfAddZeroRight (qnfMul factor qnfZero)).symm.trans
        (congrArg (qnfAdd (qnfMul factor qnfZero))
          (qnfAddNegRight (qnfMul factor qnfZero)).symm)).trans
      (qnfAddAssoc (qnfMul factor qnfZero) (qnfMul factor qnfZero)
        (qnfNeg (qnfMul factor qnfZero))).symm).trans
    (congrArg (fun value => qnfAdd value (qnfNeg (qnfMul factor qnfZero)))
      ((qnfMulLeftDistrib factor qnfZero qnfZero).symm.trans
        (congrArg (qnfMul factor) (qnfAddZeroLeft qnfZero))))).trans
    (qnfAddNegRight (qnfMul factor qnfZero))

/-- Multiplying the canonical zero on the left annihilates. -/
theorem grqQnfMulZeroLeft (factor : QnfRat) : qnfMul qnfZero factor = qnfZero :=
  (qnfMulComm qnfZero factor).trans (grqQnfMulZeroRight factor)

/-- A negated left factor negates the product. -/
theorem grqQnfMulNegLeft (factor otherValue : QnfRat) :
    qnfMul (qnfNeg factor) otherValue = qnfNeg (qnfMul factor otherValue) :=
  (grqQnfNegEqOfAddEqZero
    (((qnfMulRightDistrib factor (qnfNeg factor) otherValue).symm.trans
        (congrArg (fun value => qnfMul value otherValue) (qnfAddNegRight factor))).trans
      (grqQnfMulZeroLeft otherValue))).symm

/-! ## Terms and polynomials over QnfRat: sorted coefficient-carrying lists -/

/-- One polynomial term: a canonical rational coefficient on an exponent vector
(the F2 collapse "stored monomial = coefficient 1" is undone). -/
structure GrqTerm where
  coefficient : QnfRat
  exponentVector : GrbExp

/-- Structural Boolean equality on terms — canonical-coefficient comparison AND
exponent-vector comparison; byte equality IS semantic equality on both components. -/
def grqTermBeq (leftTerm rightTerm : GrqTerm) : Bool :=
  qnfBeq leftTerm.coefficient rightTerm.coefficient &&
    grbExpBeq leftTerm.exponentVector rightTerm.exponentVector

/-- Reflexivity of `grqTermBeq`. -/
theorem grqTermBeqRefl (term : GrqTerm) : grqTermBeq term term = true := by
  show (qnfBeq term.coefficient term.coefficient &&
    grbExpBeq term.exponentVector term.exponentVector) = true
  rw [qnfBeqSelfIsTrue term.coefficient, grbExpBeqRefl term.exponentVector]
  rfl

/-- `grqTermBeq` sound: beq-true terms are equal. -/
theorem grqTermBeqEq : (leftTerm rightTerm : GrqTerm) →
    grqTermBeq leftTerm rightTerm = true → leftTerm = rightTerm
  | GrqTerm.mk leftCoefficient leftExponent, GrqTerm.mk rightCoefficient rightExponent,
      hBeq => by
      have hSplit := grbBoolAndElim _ _ hBeq
      rw [(qnfBeqIffEq leftCoefficient rightCoefficient).mp hSplit.left,
        grbExpBeqEq leftExponent rightExponent hSplit.right]

/-- A rational polynomial: terms sorted strictly descending under `grbMonoLess`
with all stored coefficients nonzero — maintained computationally by
`grqTermInsert`, certified by `GrqPolyCanonical`. -/
abbrev GrqPoly := List GrqTerm

/-- Structural Boolean equality on polynomials. -/
def grqPolyBeq : GrqPoly → GrqPoly → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest =>
      grqTermBeq leftHead rightHead && grqPolyBeq leftRest rightRest

/-- Reflexivity of `grqPolyBeq`. -/
theorem grqPolyBeqRefl : (poly : GrqPoly) → grqPolyBeq poly poly = true
  | [] => rfl
  | head :: rest => by
      show (grqTermBeq head head && grqPolyBeq rest rest) = true
      rw [grqTermBeqRefl head, grqPolyBeqRefl rest]
      rfl

/-- `grqPolyBeq` sound: beq-true polynomials are equal. -/
theorem grqPolyBeqEq : (leftPoly rightPoly : GrqPoly) →
    grqPolyBeq leftPoly rightPoly = true → leftPoly = rightPoly
  | [], [], _ => rfl
  | [], _ :: _, hBeq => Bool.noConfusion hBeq
  | _ :: _, [], hBeq => Bool.noConfusion hBeq
  | leftHead :: leftRest, rightHead :: rightRest, hBeq => by
      have hSplit := grbBoolAndElim _ _ hBeq
      rw [grqTermBeqEq leftHead rightHead hSplit.left,
        grqPolyBeqEq leftRest rightRest hSplit.right]

/-- The zero polynomial. -/
def grqZeroPoly : GrqPoly := []

/-- The constant-one polynomial. -/
def grqOnePoly : GrqPoly := [{ coefficient := qnfOne, exponentVector := [] }]

/-- The degree-one monic polynomial in a single variable. -/
def grqVariablePoly (index : Nat) : GrqPoly :=
  [{ coefficient := qnfOne,
     exponentVector := [{ variableIndex := index, exponent := 1 }] }]

/-! ## Term insertion: the four-way canonical merge -/

/-- Insert a coefficient-carrying term into a polynomial: a zero coefficient is a
no-op; a collision ADDS coefficients (dropping the pair when the sum vanishes —
the decidable stripping the canonical carrier buys); otherwise place by the
descending monomial order. -/
def grqTermInsert (coefficient : QnfRat) (exponent : GrbExp) : GrqPoly → GrqPoly
  | [] =>
      cond (qnfBeq coefficient qnfZero) []
        [{ coefficient := coefficient, exponentVector := exponent }]
  | head :: rest =>
      cond (qnfBeq coefficient qnfZero)
        (head :: rest)
        (cond (grbExpBeq exponent head.exponentVector)
          (cond (qnfBeq (qnfAdd coefficient head.coefficient) qnfZero)
            rest
            ({ coefficient := qnfAdd coefficient head.coefficient,
               exponentVector := head.exponentVector } :: rest))
          (cond (grbMonoLess head.exponentVector exponent)
            ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest)
            (head :: grqTermInsert coefficient exponent rest)))

/-- `grqTermInsert` branch: zero coefficient into nil — no-op. -/
theorem grqTermInsertNilOnZeroCoefficient (coefficient : QnfRat) (exponent : GrbExp)
    (hZero : qnfBeq coefficient qnfZero = true) :
    grqTermInsert coefficient exponent [] = [] := by
  show cond (qnfBeq coefficient qnfZero) []
      ([{ coefficient := coefficient, exponentVector := exponent }] : GrqPoly) = []
  rw [hZero]
  rfl

/-- `grqTermInsert` branch: nonzero coefficient into nil — singleton. -/
theorem grqTermInsertNilOnNonzeroCoefficient (coefficient : QnfRat) (exponent : GrbExp)
    (hNonzero : qnfBeq coefficient qnfZero = false) :
    grqTermInsert coefficient exponent [] =
      [{ coefficient := coefficient, exponentVector := exponent }] := by
  show cond (qnfBeq coefficient qnfZero) []
      ([{ coefficient := coefficient, exponentVector := exponent }] : GrqPoly) =
    [{ coefficient := coefficient, exponentVector := exponent }]
  rw [hNonzero]
  rfl

/-- `grqTermInsert` branch: zero coefficient — no-op. -/
theorem grqTermInsertOnZeroCoefficient (coefficient : QnfRat) (exponent : GrbExp)
    (head : GrqTerm) (rest : GrqPoly)
    (hZero : qnfBeq coefficient qnfZero = true) :
    grqTermInsert coefficient exponent (head :: rest) = head :: rest := by
  show cond (qnfBeq coefficient qnfZero)
      (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector)
        (cond (qnfBeq (qnfAdd coefficient head.coefficient) qnfZero)
          rest
          ({ coefficient := qnfAdd coefficient head.coefficient,
             exponentVector := head.exponentVector } :: rest))
        (cond (grbMonoLess head.exponentVector exponent)
          ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest)
          (head :: grqTermInsert coefficient exponent rest))) = head :: rest
  rw [hZero]
  rfl

/-- `grqTermInsert` branch: collision with vanishing sum — the pair cancels. -/
theorem grqTermInsertOnCollisionCancel (coefficient : QnfRat) (exponent : GrbExp)
    (head : GrqTerm) (rest : GrqPoly)
    (hNonzero : qnfBeq coefficient qnfZero = false)
    (hShared : grbExpBeq exponent head.exponentVector = true)
    (hSumZero : qnfBeq (qnfAdd coefficient head.coefficient) qnfZero = true) :
    grqTermInsert coefficient exponent (head :: rest) = rest := by
  show cond (qnfBeq coefficient qnfZero)
      (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector)
        (cond (qnfBeq (qnfAdd coefficient head.coefficient) qnfZero)
          rest
          ({ coefficient := qnfAdd coefficient head.coefficient,
             exponentVector := head.exponentVector } :: rest))
        (cond (grbMonoLess head.exponentVector exponent)
          ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest)
          (head :: grqTermInsert coefficient exponent rest))) = rest
  rw [hNonzero, hShared, hSumZero]
  rfl

/-- `grqTermInsert` branch: collision with surviving sum — coefficients merge. -/
theorem grqTermInsertOnCollisionMerge (coefficient : QnfRat) (exponent : GrbExp)
    (head : GrqTerm) (rest : GrqPoly)
    (hNonzero : qnfBeq coefficient qnfZero = false)
    (hShared : grbExpBeq exponent head.exponentVector = true)
    (hSumNonzero : qnfBeq (qnfAdd coefficient head.coefficient) qnfZero = false) :
    grqTermInsert coefficient exponent (head :: rest) =
      { coefficient := qnfAdd coefficient head.coefficient,
        exponentVector := head.exponentVector } :: rest := by
  show cond (qnfBeq coefficient qnfZero)
      (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector)
        (cond (qnfBeq (qnfAdd coefficient head.coefficient) qnfZero)
          rest
          ({ coefficient := qnfAdd coefficient head.coefficient,
             exponentVector := head.exponentVector } :: rest))
        (cond (grbMonoLess head.exponentVector exponent)
          ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest)
          (head :: grqTermInsert coefficient exponent rest))) =
    { coefficient := qnfAdd coefficient head.coefficient,
      exponentVector := head.exponentVector } :: rest
  rw [hNonzero, hShared, hSumNonzero]
  rfl

/-- `grqTermInsert` branch: the inserted exponent dominates the head — prepend. -/
theorem grqTermInsertOnGreater (coefficient : QnfRat) (exponent : GrbExp)
    (head : GrqTerm) (rest : GrqPoly)
    (hNonzero : qnfBeq coefficient qnfZero = false)
    (hDistinct : grbExpBeq exponent head.exponentVector = false)
    (hHeadLess : grbMonoLess head.exponentVector exponent = true) :
    grqTermInsert coefficient exponent (head :: rest) =
      { coefficient := coefficient, exponentVector := exponent } :: head :: rest := by
  show cond (qnfBeq coefficient qnfZero)
      (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector)
        (cond (qnfBeq (qnfAdd coefficient head.coefficient) qnfZero)
          rest
          ({ coefficient := qnfAdd coefficient head.coefficient,
             exponentVector := head.exponentVector } :: rest))
        (cond (grbMonoLess head.exponentVector exponent)
          ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest)
          (head :: grqTermInsert coefficient exponent rest))) =
    { coefficient := coefficient, exponentVector := exponent } :: head :: rest
  rw [hNonzero, hDistinct, hHeadLess]
  rfl

/-- `grqTermInsert` branch: the head dominates — descend. -/
theorem grqTermInsertOnSmaller (coefficient : QnfRat) (exponent : GrbExp)
    (head : GrqTerm) (rest : GrqPoly)
    (hNonzero : qnfBeq coefficient qnfZero = false)
    (hDistinct : grbExpBeq exponent head.exponentVector = false)
    (hNotGreater : grbMonoLess head.exponentVector exponent = false) :
    grqTermInsert coefficient exponent (head :: rest) =
      head :: grqTermInsert coefficient exponent rest := by
  show cond (qnfBeq coefficient qnfZero)
      (head :: rest)
      (cond (grbExpBeq exponent head.exponentVector)
        (cond (qnfBeq (qnfAdd coefficient head.coefficient) qnfZero)
          rest
          ({ coefficient := qnfAdd coefficient head.coefficient,
             exponentVector := head.exponentVector } :: rest))
        (cond (grbMonoLess head.exponentVector exponent)
          ({ coefficient := coefficient, exponentVector := exponent } :: head :: rest)
          (head :: grqTermInsert coefficient exponent rest))) =
    head :: grqTermInsert coefficient exponent rest
  rw [hNonzero, hDistinct, hNotGreater]
  rfl

/-! ## Arithmetic: insert-fold addition, negation, term scaling, multiplication -/

/-- Polynomial addition: insert-fold the left list into the right.
`grqAdd [] right = right` is definitional, and the result is canonical whenever
`right` is — for ANY left operand (`grqAddKeepsCanonical`). -/
def grqAdd : GrqPoly → GrqPoly → GrqPoly
  | [], right => right
  | term :: rest, right =>
      grqTermInsert term.coefficient term.exponentVector (grqAdd rest right)

/-- Polynomial negation: negate every coefficient (exponents untouched). -/
def grqNeg : GrqPoly → GrqPoly
  | [] => []
  | term :: rest =>
      { coefficient := qnfNeg term.coefficient,
        exponentVector := term.exponentVector } :: grqNeg rest

/-- Multiply every term of a polynomial by a fixed coefficient and monomial —
the single-term product `scalar·monomial · poly` (no re-sorting; consumers fold the
result through `grqAdd`, whose right operand carries canonicity). -/
def grqScaleTerm (scalar : QnfRat) (monomial : GrbExp) : GrqPoly → GrqPoly
  | [] => []
  | term :: rest =>
      { coefficient := qnfMul scalar term.coefficient,
        exponentVector := grbExpMul monomial term.exponentVector } ::
        grqScaleTerm scalar monomial rest

/-- Polynomial multiplication: distribute `grqScaleTerm` over `grqAdd`. -/
def grqMul : GrqPoly → GrqPoly → GrqPoly
  | [], [] => []
  | [], _ :: _ => []
  | term :: rest, right =>
      grqAdd (grqScaleTerm term.coefficient term.exponentVector right) (grqMul rest right)

/-- `grqMul [] right = []` for every right operand. -/
theorem grqMulNilLeft : (right : GrqPoly) → grqMul [] right = []
  | [] => rfl
  | _ :: _ => rfl

/-- Sum of pairwise products `Σ cofᵢ·genᵢ` (mismatched lengths truncate to zero). -/
def grqSumOfProducts : List GrqPoly → List GrqPoly → GrqPoly
  | [], [] => []
  | [], _ :: _ => []
  | _ :: _, [] => []
  | cofactor :: cofactorRest, gen :: genRest =>
      grqAdd (grqMul cofactor gen) (grqSumOfProducts cofactorRest genRest)

/-! ## Canonicity: strict descent plus nonzero coefficients -/

/-- The canonical-form invariant: exponent vectors strictly descending under
`grbMonoLess` AND every stored coefficient nonzero. -/
inductive GrqPolyCanonical : GrqPoly → Prop where
  | nilIsCanonical : GrqPolyCanonical []
  | singleIsCanonical (term : GrqTerm)
      (isNonzero : qnfBeq term.coefficient qnfZero = false) :
      GrqPolyCanonical [term]
  | consIsCanonical (first second : GrqTerm) (rest : GrqPoly)
      (isNonzero : qnfBeq first.coefficient qnfZero = false)
      (isDescending : grbMonoLess second.exponentVector first.exponentVector = true)
      (tailIsCanonical : GrqPolyCanonical (second :: rest)) :
      GrqPolyCanonical (first :: second :: rest)

/-- The head coefficient of a canonical list is nonzero. -/
theorem grqCanonicalHeadNonzero (head : GrqTerm) (rest : GrqPoly)
    (hCanonical : GrqPolyCanonical (head :: rest)) :
    qnfBeq head.coefficient qnfZero = false := by
  cases hCanonical with
  | singleIsCanonical _ isNonzero => exact isNonzero
  | consIsCanonical _ _ _ isNonzero _ _ => exact isNonzero

/-- The tail of a canonical list is canonical. -/
theorem grqCanonicalTail (head : GrqTerm) (rest : GrqPoly)
    (hCanonical : GrqPolyCanonical (head :: rest)) : GrqPolyCanonical rest := by
  cases hCanonical with
  | singleIsCanonical _ _ => exact GrqPolyCanonical.nilIsCanonical
  | consIsCanonical _ _ _ _ _ tailIsCanonical => exact tailIsCanonical

/-- Dropping the second element of a canonical list keeps it canonical. -/
theorem grqCanonicalSkip (first second : GrqTerm) (rest : GrqPoly)
    (hCanonical : GrqPolyCanonical (first :: second :: rest)) :
    GrqPolyCanonical (first :: rest) := by
  cases hCanonical with
  | consIsCanonical _ _ _ isNonzero isDescending tailIsCanonical =>
      cases tailIsCanonical with
      | singleIsCanonical _ _ =>
          exact GrqPolyCanonical.singleIsCanonical first isNonzero
      | consIsCanonical _ _ _ _ isDescendingTail tailTailIsCanonical =>
          exact GrqPolyCanonical.consIsCanonical _ _ _ isNonzero
            (grbMonoLessTrans _ _ _ isDescendingTail isDescending) tailTailIsCanonical

/-- Replacing the head coefficient of a canonical list by any nonzero coefficient
(same exponent vector) keeps it canonical — the collision-merge shape. -/
theorem grqCanonicalReplaceHeadCoefficient (newCoefficient : QnfRat)
    (head : GrqTerm) (rest : GrqPoly)
    (isNonzero : qnfBeq newCoefficient qnfZero = false)
    (hCanonical : GrqPolyCanonical (head :: rest)) :
    GrqPolyCanonical
      ({ coefficient := newCoefficient, exponentVector := head.exponentVector } :: rest) := by
  cases hCanonical with
  | singleIsCanonical _ _ =>
      exact GrqPolyCanonical.singleIsCanonical _ isNonzero
  | consIsCanonical _ second tailRest _ isDescending tailIsCanonical =>
      exact GrqPolyCanonical.consIsCanonical _ second tailRest isNonzero
        isDescending tailIsCanonical

/-- Inserting a term strictly below a dominating head keeps the list canonical. -/
theorem grqTermInsertUnderHead : (rest : GrqPoly) → (head : GrqTerm) →
    (coefficient : QnfRat) → (exponent : GrbExp) →
    grbMonoLess exponent head.exponentVector = true →
    GrqPolyCanonical (head :: rest) →
    GrqPolyCanonical (head :: grqTermInsert coefficient exponent rest)
  | [], head, coefficient, exponent, hUnderHead, hCanonical => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertNilOnZeroCoefficient coefficient exponent hZero]
          exact hCanonical
      | false =>
          rw [grqTermInsertNilOnNonzeroCoefficient coefficient exponent hZero]
          exact GrqPolyCanonical.consIsCanonical head _ []
            (grqCanonicalHeadNonzero head [] hCanonical) hUnderHead
            (GrqPolyCanonical.singleIsCanonical _ hZero)
  | second :: rest2, head, coefficient, exponent, hUnderHead, hCanonical => by
      cases hCanonical with
      | consIsCanonical _ _ _ hHeadNonzero hSecondLess hTailCanonical =>
          cases hZero : qnfBeq coefficient qnfZero with
          | true =>
              rw [grqTermInsertOnZeroCoefficient coefficient exponent second rest2 hZero]
              exact GrqPolyCanonical.consIsCanonical head second rest2 hHeadNonzero
                hSecondLess hTailCanonical
          | false =>
              cases hShared : grbExpBeq exponent second.exponentVector with
              | true =>
                  cases hSum : qnfBeq (qnfAdd coefficient second.coefficient) qnfZero with
                  | true =>
                      rw [grqTermInsertOnCollisionCancel coefficient exponent second rest2
                        hZero hShared hSum]
                      exact grqCanonicalSkip head second rest2
                        (GrqPolyCanonical.consIsCanonical head second rest2 hHeadNonzero
                          hSecondLess hTailCanonical)
                  | false =>
                      rw [grqTermInsertOnCollisionMerge coefficient exponent second rest2
                        hZero hShared hSum]
                      exact GrqPolyCanonical.consIsCanonical head _ rest2 hHeadNonzero
                        hSecondLess
                        (grqCanonicalReplaceHeadCoefficient _ second rest2 hSum
                          hTailCanonical)
              | false =>
                  cases hLess : grbMonoLess second.exponentVector exponent with
                  | true =>
                      rw [grqTermInsertOnGreater coefficient exponent second rest2
                        hZero hShared hLess]
                      exact GrqPolyCanonical.consIsCanonical head _ _ hHeadNonzero
                        hUnderHead
                        (GrqPolyCanonical.consIsCanonical _ second rest2 hZero hLess
                          hTailCanonical)
                  | false =>
                      have hUnderSecond : grbMonoLess exponent second.exponentVector = true := by
                        cases grbMonoLessTotal exponent second.exponentVector hShared with
                        | inl hForward => exact hForward
                        | inr hBackward => exact Bool.noConfusion (hLess.symm.trans hBackward)
                      rw [grqTermInsertOnSmaller coefficient exponent second rest2
                        hZero hShared hLess]
                      exact GrqPolyCanonical.consIsCanonical head second _ hHeadNonzero
                        hSecondLess
                        (grqTermInsertUnderHead rest2 second coefficient exponent
                          hUnderSecond hTailCanonical)

/-- `grqTermInsert` preserves canonicity — for ANY inserted coefficient. -/
theorem grqTermInsertKeepsCanonical (coefficient : QnfRat) (exponent : GrbExp) :
    (poly : GrqPoly) → GrqPolyCanonical poly →
    GrqPolyCanonical (grqTermInsert coefficient exponent poly)
  | [], _ => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertNilOnZeroCoefficient coefficient exponent hZero]
          exact GrqPolyCanonical.nilIsCanonical
      | false =>
          rw [grqTermInsertNilOnNonzeroCoefficient coefficient exponent hZero]
          exact GrqPolyCanonical.singleIsCanonical _ hZero
  | head :: rest, hCanonical => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertOnZeroCoefficient coefficient exponent head rest hZero]
          exact hCanonical
      | false =>
          cases hShared : grbExpBeq exponent head.exponentVector with
          | true =>
              cases hSum : qnfBeq (qnfAdd coefficient head.coefficient) qnfZero with
              | true =>
                  rw [grqTermInsertOnCollisionCancel coefficient exponent head rest
                    hZero hShared hSum]
                  exact grqCanonicalTail head rest hCanonical
              | false =>
                  rw [grqTermInsertOnCollisionMerge coefficient exponent head rest
                    hZero hShared hSum]
                  exact grqCanonicalReplaceHeadCoefficient _ head rest hSum hCanonical
          | false =>
              cases hLess : grbMonoLess head.exponentVector exponent with
              | true =>
                  rw [grqTermInsertOnGreater coefficient exponent head rest
                    hZero hShared hLess]
                  exact GrqPolyCanonical.consIsCanonical _ head rest hZero hLess hCanonical
              | false =>
                  have hUnderHead : grbMonoLess exponent head.exponentVector = true := by
                    cases grbMonoLessTotal exponent head.exponentVector hShared with
                    | inl hForward => exact hForward
                    | inr hBackward => exact Bool.noConfusion (hLess.symm.trans hBackward)
                  rw [grqTermInsertOnSmaller coefficient exponent head rest
                    hZero hShared hLess]
                  exact grqTermInsertUnderHead rest head coefficient exponent
                    hUnderHead hCanonical

/-- `grqAdd left right` is canonical whenever `right` is — for ANY left operand. -/
theorem grqAddKeepsCanonical : (leftPoly rightPoly : GrqPoly) →
    GrqPolyCanonical rightPoly → GrqPolyCanonical (grqAdd leftPoly rightPoly)
  | [], _, hRightCanonical => hRightCanonical
  | term :: rest, rightPoly, hRightCanonical =>
      grqTermInsertKeepsCanonical term.coefficient term.exponentVector
        (grqAdd rest rightPoly)
        (grqAddKeepsCanonical rest rightPoly hRightCanonical)

/-- `grqMul` output is unconditionally canonical. -/
theorem grqMulIsCanonical : (leftPoly rightPoly : GrqPoly) →
    GrqPolyCanonical (grqMul leftPoly rightPoly)
  | [], [] => GrqPolyCanonical.nilIsCanonical
  | [], _ :: _ => GrqPolyCanonical.nilIsCanonical
  | term :: rest, rightPoly =>
      grqAddKeepsCanonical (grqScaleTerm term.coefficient term.exponentVector rightPoly)
        (grqMul rest rightPoly) (grqMulIsCanonical rest rightPoly)

/-- `grqSumOfProducts` output is unconditionally canonical. -/
theorem grqSumOfProductsIsCanonical : (cofactors generators : List GrqPoly) →
    GrqPolyCanonical (grqSumOfProducts cofactors generators)
  | [], [] => GrqPolyCanonical.nilIsCanonical
  | [], _ :: _ => GrqPolyCanonical.nilIsCanonical
  | _ :: _, [] => GrqPolyCanonical.nilIsCanonical
  | cofactor :: cofactorRest, gen :: genRest =>
      grqAddKeepsCanonical (grqMul cofactor gen) (grqSumOfProducts cofactorRest genRest)
        (grqSumOfProductsIsCanonical cofactorRest genRest)

/-! ## The QnfRat coefficient scan and canonical-list extensionality

`grqCoeff` is the coefficient function — a `qnfAdd` homomorphism from ARBITRARY
term lists; on canonical lists it is the exact coefficient, and two canonical lists
with pointwise-equal coefficient functions are byte-equal
(`grqPolyExtensionality`).  Every AC identity downstream is one extensionality fire
over a hand-telescoped `qnf` law chain. -/

/-- The contribution of one term to the coefficient at a probe exponent. -/
def grqTermCoeffAt (term : GrqTerm) (probe : GrbExp) : QnfRat :=
  cond (grbExpBeq probe term.exponentVector) term.coefficient qnfZero

/-- QnfRat coefficient of a probe exponent in a polynomial (additive scan). -/
def grqCoeff : GrqPoly → GrbExp → QnfRat
  | [], _ => qnfZero
  | term :: rest, probe => qnfAdd (grqTermCoeffAt term probe) (grqCoeff rest probe)

/-- Coefficient scan through a term insertion — on ARBITRARY lists. -/
theorem grqCoeffTermInsert : (poly : GrqPoly) → (coefficient : QnfRat) →
    (exponent probe : GrbExp) →
    grqCoeff (grqTermInsert coefficient exponent poly) probe =
      qnfAdd (cond (grbExpBeq probe exponent) coefficient qnfZero) (grqCoeff poly probe)
  | [], coefficient, exponent, probe => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertNilOnZeroCoefficient coefficient exponent hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero]
          show qnfZero = qnfAdd (cond (grbExpBeq probe exponent) qnfZero qnfZero) qnfZero
          exact ((qnfAddZeroRight
              (cond (grbExpBeq probe exponent) qnfZero qnfZero)).trans
            (grqCondQnfZeroBothArms (grbExpBeq probe exponent))).symm
      | false =>
          rw [grqTermInsertNilOnNonzeroCoefficient coefficient exponent hZero]
          rfl
  | head :: rest, coefficient, exponent, probe => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertOnZeroCoefficient coefficient exponent head rest hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero]
          show grqCoeff (head :: rest) probe =
            qnfAdd (cond (grbExpBeq probe exponent) qnfZero qnfZero)
              (grqCoeff (head :: rest) probe)
          exact ((congrArg (fun value => qnfAdd value (grqCoeff (head :: rest) probe))
              (grqCondQnfZeroBothArms (grbExpBeq probe exponent))).trans
            (qnfAddZeroLeft (grqCoeff (head :: rest) probe))).symm
      | false =>
          cases hShared : grbExpBeq exponent head.exponentVector with
          | true =>
              have expEq := grbExpBeqEq exponent head.exponentVector hShared
              cases hSum : qnfBeq (qnfAdd coefficient head.coefficient) qnfZero with
              | true =>
                  rw [grqTermInsertOnCollisionCancel coefficient exponent head rest
                    hZero hShared hSum, expEq]
                  show grqCoeff rest probe =
                    qnfAdd (cond (grbExpBeq probe head.exponentVector) coefficient qnfZero)
                      (qnfAdd (cond (grbExpBeq probe head.exponentVector)
                        head.coefficient qnfZero) (grqCoeff rest probe))
                  cases hProbe : grbExpBeq probe head.exponentVector with
                  | true =>
                      exact (((qnfAddAssoc coefficient head.coefficient
                          (grqCoeff rest probe)).symm.trans
                        (congrArg (fun value => qnfAdd value (grqCoeff rest probe))
                          ((qnfBeqIffEq (qnfAdd coefficient head.coefficient) qnfZero).mp
                            hSum))).trans
                        (qnfAddZeroLeft (grqCoeff rest probe))).symm
                  | false =>
                      exact ((qnfAddZeroLeft (qnfAdd qnfZero (grqCoeff rest probe))).trans
                        (qnfAddZeroLeft (grqCoeff rest probe))).symm
              | false =>
                  rw [grqTermInsertOnCollisionMerge coefficient exponent head rest
                    hZero hShared hSum, expEq]
                  show qnfAdd (cond (grbExpBeq probe head.exponentVector)
                      (qnfAdd coefficient head.coefficient) qnfZero) (grqCoeff rest probe) =
                    qnfAdd (cond (grbExpBeq probe head.exponentVector) coefficient qnfZero)
                      (qnfAdd (cond (grbExpBeq probe head.exponentVector)
                        head.coefficient qnfZero) (grqCoeff rest probe))
                  cases hProbe : grbExpBeq probe head.exponentVector with
                  | true =>
                      exact qnfAddAssoc coefficient head.coefficient (grqCoeff rest probe)
                  | false =>
                      exact (qnfAddZeroLeft (grqCoeff rest probe)).trans
                        (((qnfAddZeroLeft (qnfAdd qnfZero (grqCoeff rest probe))).trans
                          (qnfAddZeroLeft (grqCoeff rest probe))).symm)
          | false =>
              cases hLess : grbMonoLess head.exponentVector exponent with
              | true =>
                  rw [grqTermInsertOnGreater coefficient exponent head rest
                    hZero hShared hLess]
                  rfl
              | false =>
                  rw [grqTermInsertOnSmaller coefficient exponent head rest
                    hZero hShared hLess]
                  show qnfAdd (cond (grbExpBeq probe head.exponentVector)
                      head.coefficient qnfZero)
                      (grqCoeff (grqTermInsert coefficient exponent rest) probe) =
                    qnfAdd (cond (grbExpBeq probe exponent) coefficient qnfZero)
                      (qnfAdd (cond (grbExpBeq probe head.exponentVector)
                        head.coefficient qnfZero) (grqCoeff rest probe))
                  rw [grqCoeffTermInsert rest coefficient exponent probe]
                  exact grqQnfAddSwapLeft
                    (cond (grbExpBeq probe head.exponentVector) head.coefficient qnfZero)
                    (cond (grbExpBeq probe exponent) coefficient qnfZero)
                    (grqCoeff rest probe)

/-- The coefficient scan is a `qnfAdd` homomorphism through `grqAdd` — on
ARBITRARY lists. -/
theorem grqCoeffAdd : (leftPoly rightPoly : GrqPoly) → (probe : GrbExp) →
    grqCoeff (grqAdd leftPoly rightPoly) probe =
      qnfAdd (grqCoeff leftPoly probe) (grqCoeff rightPoly probe)
  | [], rightPoly, probe => (qnfAddZeroLeft (grqCoeff rightPoly probe)).symm
  | term :: rest, rightPoly, probe => by
      show grqCoeff (grqTermInsert term.coefficient term.exponentVector
        (grqAdd rest rightPoly)) probe = _
      rw [grqCoeffTermInsert (grqAdd rest rightPoly) term.coefficient
        term.exponentVector probe, grqCoeffAdd rest rightPoly probe]
      exact (qnfAddAssoc
        (cond (grbExpBeq probe term.exponentVector) term.coefficient qnfZero)
        (grqCoeff rest probe) (grqCoeff rightPoly probe)).symm

/-- The coefficient scan negates through `grqNeg`. -/
theorem grqCoeffNeg : (poly : GrqPoly) → (probe : GrbExp) →
    grqCoeff (grqNeg poly) probe = qnfNeg (grqCoeff poly probe)
  | [], _ => grqQnfNegZeroIsZero.symm
  | term :: rest, probe => by
      show qnfAdd (cond (grbExpBeq probe term.exponentVector)
          (qnfNeg term.coefficient) qnfZero) (grqCoeff (grqNeg rest) probe) =
        qnfNeg (qnfAdd (cond (grbExpBeq probe term.exponentVector)
          term.coefficient qnfZero) (grqCoeff rest probe))
      rw [grqCoeffNeg rest probe,
        grqQnfNegAddDistrib
          (cond (grbExpBeq probe term.exponentVector) term.coefficient qnfZero)
          (grqCoeff rest probe)]
      exact congrArg (fun value => qnfAdd value (qnfNeg (grqCoeff rest probe)))
        (grqQnfNegCondZero (grbExpBeq probe term.exponentVector) term.coefficient).symm

/-- Scaling by the zero coefficient scans to zero everywhere. -/
theorem grqCoeffScaleTermZero : (gen : GrqPoly) → (monomial probe : GrbExp) →
    grqCoeff (grqScaleTerm qnfZero monomial gen) probe = qnfZero
  | [], _, _ => rfl
  | term :: rest, monomial, probe => by
      show qnfAdd (cond (grbExpBeq probe (grbExpMul monomial term.exponentVector))
          (qnfMul qnfZero term.coefficient) qnfZero)
        (grqCoeff (grqScaleTerm qnfZero monomial rest) probe) = qnfZero
      rw [grqCoeffScaleTermZero rest monomial probe, grqQnfMulZeroLeft term.coefficient]
      exact (qnfAddZeroRight
          (cond (grbExpBeq probe (grbExpMul monomial term.exponentVector))
            qnfZero qnfZero)).trans
        (grqCondQnfZeroBothArms (grbExpBeq probe (grbExpMul monomial term.exponentVector)))

/-- Scaling by a coefficient SUM scans to the sum of the scans — the pointwise
distributivity the collision-merge case of the cofactor-update law consumes. -/
theorem grqCoeffScaleTermAddCoeff : (gen : GrqPoly) → (leftScalar rightScalar : QnfRat) →
    (monomial probe : GrbExp) →
    grqCoeff (grqScaleTerm (qnfAdd leftScalar rightScalar) monomial gen) probe =
      qnfAdd (grqCoeff (grqScaleTerm leftScalar monomial gen) probe)
        (grqCoeff (grqScaleTerm rightScalar monomial gen) probe)
  | [], _, _, _, _ => (qnfAddZeroLeft qnfZero).symm
  | term :: rest, leftScalar, rightScalar, monomial, probe => by
      show qnfAdd (cond (grbExpBeq probe (grbExpMul monomial term.exponentVector))
            (qnfMul (qnfAdd leftScalar rightScalar) term.coefficient) qnfZero)
          (grqCoeff (grqScaleTerm (qnfAdd leftScalar rightScalar) monomial rest) probe) =
        qnfAdd
          (qnfAdd (cond (grbExpBeq probe (grbExpMul monomial term.exponentVector))
              (qnfMul leftScalar term.coefficient) qnfZero)
            (grqCoeff (grqScaleTerm leftScalar monomial rest) probe))
          (qnfAdd (cond (grbExpBeq probe (grbExpMul monomial term.exponentVector))
              (qnfMul rightScalar term.coefficient) qnfZero)
            (grqCoeff (grqScaleTerm rightScalar monomial rest) probe))
      rw [grqCoeffScaleTermAddCoeff rest leftScalar rightScalar monomial probe]
      cases hProbe : grbExpBeq probe (grbExpMul monomial term.exponentVector) with
      | true =>
          exact (congrArg
              (fun value => qnfAdd value
                (qnfAdd (grqCoeff (grqScaleTerm leftScalar monomial rest) probe)
                  (grqCoeff (grqScaleTerm rightScalar monomial rest) probe)))
              (qnfMulRightDistrib leftScalar rightScalar term.coefficient)).trans
            (grqQnfAddExchange (qnfMul leftScalar term.coefficient)
              (qnfMul rightScalar term.coefficient)
              (grqCoeff (grqScaleTerm leftScalar monomial rest) probe)
              (grqCoeff (grqScaleTerm rightScalar monomial rest) probe))
      | false =>
          exact (qnfAddZeroLeft
              (qnfAdd (grqCoeff (grqScaleTerm leftScalar monomial rest) probe)
                (grqCoeff (grqScaleTerm rightScalar monomial rest) probe))).trans
            (((congrArg (fun value => qnfAdd value
                  (qnfAdd qnfZero (grqCoeff (grqScaleTerm rightScalar monomial rest) probe)))
                (qnfAddZeroLeft
                  (grqCoeff (grqScaleTerm leftScalar monomial rest) probe))).trans
              (congrArg (qnfAdd (grqCoeff (grqScaleTerm leftScalar monomial rest) probe))
                (qnfAddZeroLeft
                  (grqCoeff (grqScaleTerm rightScalar monomial rest) probe)))).symm)

/-- Scaling by a NEGATED coefficient is the negation of the scaled polynomial —
structural list equality, no extensionality needed. -/
theorem grqScaleTermNegCoeff : (gen : GrqPoly) → (scalar : QnfRat) → (monomial : GrbExp) →
    grqScaleTerm (qnfNeg scalar) monomial gen = grqNeg (grqScaleTerm scalar monomial gen)
  | [], _, _ => rfl
  | term :: rest, scalar, monomial => by
      show ({ coefficient := qnfMul (qnfNeg scalar) term.coefficient,
              exponentVector := grbExpMul monomial term.exponentVector } : GrqTerm) ::
          grqScaleTerm (qnfNeg scalar) monomial rest =
        { coefficient := qnfNeg (qnfMul scalar term.coefficient),
          exponentVector := grbExpMul monomial term.exponentVector } ::
          grqNeg (grqScaleTerm scalar monomial rest)
      rw [grqQnfMulNegLeft scalar term.coefficient, grqScaleTermNegCoeff rest scalar monomial]

/-- In a canonical list, the tail scans to zero at the head's own exponent. -/
theorem grqCoeffZeroUnderHead : (tail : GrqPoly) → (head : GrqTerm) →
    GrqPolyCanonical (head :: tail) → grqCoeff tail head.exponentVector = qnfZero
  | [], _, _ => rfl
  | second :: rest, head, hCanonical => by
      cases hCanonical with
      | consIsCanonical _ _ _ hHeadNonzero hSecondLess hTailCanonical =>
          have hBeqFalse : grbExpBeq head.exponentVector second.exponentVector = false := by
            cases hBeqCheck : grbExpBeq head.exponentVector second.exponentVector with
            | false => rfl
            | true =>
                have expEq := grbExpBeqEq head.exponentVector second.exponentVector hBeqCheck
                rw [← expEq] at hSecondLess
                rw [grbMonoLessIrrefl head.exponentVector] at hSecondLess
                exact Bool.noConfusion hSecondLess
          show qnfAdd (cond (grbExpBeq head.exponentVector second.exponentVector)
              second.coefficient qnfZero) (grqCoeff rest head.exponentVector) = qnfZero
          rw [hBeqFalse,
            grqCoeffZeroUnderHead rest head
              (grqCanonicalSkip head second rest
                (GrqPolyCanonical.consIsCanonical head second rest hHeadNonzero
                  hSecondLess hTailCanonical))]
          exact qnfAddZeroLeft qnfZero

/-- The scan of a canonical list at its own head exponent IS the head
coefficient — the exactness that makes the scan the true coefficient function. -/
theorem grqCoeffHeadIsCoefficient (head : GrqTerm) (tail : GrqPoly)
    (hCanonical : GrqPolyCanonical (head :: tail)) :
    grqCoeff (head :: tail) head.exponentVector = head.coefficient := by
  show qnfAdd (cond (grbExpBeq head.exponentVector head.exponentVector)
      head.coefficient qnfZero) (grqCoeff tail head.exponentVector) = head.coefficient
  rw [grbExpBeqRefl head.exponentVector, grqCoeffZeroUnderHead tail head hCanonical]
  exact qnfAddZeroRight head.coefficient

/-- A probe with nonzero coefficient in a canonical tail sits strictly below the
head exponent. -/
theorem grqCoeffNonzeroImpliesLessThanHead : (tail : GrqPoly) → (head : GrqTerm) →
    (probe : GrbExp) → GrqPolyCanonical (head :: tail) →
    (grqCoeff tail probe = qnfZero → False) →
    grbMonoLess probe head.exponentVector = true
  | [], _, _, _, isNonzero => False.elim (isNonzero rfl)
  | second :: rest, head, probe, hCanonical, isNonzero => by
      cases hCanonical with
      | consIsCanonical _ _ _ hHeadNonzero hSecondLess hTailCanonical =>
          cases hProbe : grbExpBeq probe second.exponentVector with
          | true =>
              rw [grbExpBeqEq probe second.exponentVector hProbe]
              exact hSecondLess
          | false =>
              have tailNonzero : grqCoeff rest probe = qnfZero → False := by
                intro tailZero
                apply isNonzero
                show qnfAdd (cond (grbExpBeq probe second.exponentVector)
                    second.coefficient qnfZero) (grqCoeff rest probe) = qnfZero
                rw [hProbe, tailZero]
                exact qnfAddZeroLeft qnfZero
              exact grbMonoLessTrans probe second.exponentVector head.exponentVector
                (grqCoeffNonzeroImpliesLessThanHead rest second probe hTailCanonical
                  tailNonzero)
                hSecondLess

/-- **Canonical-list extensionality**: canonical polynomials with pointwise-equal
QnfRat coefficient functions are byte-equal lists — the T1 keystone, structurally
true BECAUSE the coefficients are canonical. -/
theorem grqPolyExtensionality : (leftPoly rightPoly : GrqPoly) →
    GrqPolyCanonical leftPoly → GrqPolyCanonical rightPoly →
    ((probe : GrbExp) → grqCoeff leftPoly probe = grqCoeff rightPoly probe) →
    leftPoly = rightPoly
  | [], [], _, _, _ => rfl
  | [], headRight :: restRight, _, hRightCanonical, hPointwise => by
      exfalso
      have hZeroCoeff : headRight.coefficient = qnfZero :=
        (grqCoeffHeadIsCoefficient headRight restRight hRightCanonical).symm.trans
          (hPointwise headRight.exponentVector).symm
      have hNonzeroFlag := grqCanonicalHeadNonzero headRight restRight hRightCanonical
      rw [hZeroCoeff] at hNonzeroFlag
      exact Bool.noConfusion ((qnfBeqSelfIsTrue qnfZero).symm.trans hNonzeroFlag)
  | headLeft :: restLeft, [], hLeftCanonical, _, hPointwise => by
      exfalso
      have hZeroCoeff : headLeft.coefficient = qnfZero :=
        (grqCoeffHeadIsCoefficient headLeft restLeft hLeftCanonical).symm.trans
          (hPointwise headLeft.exponentVector)
      have hNonzeroFlag := grqCanonicalHeadNonzero headLeft restLeft hLeftCanonical
      rw [hZeroCoeff] at hNonzeroFlag
      exact Bool.noConfusion ((qnfBeqSelfIsTrue qnfZero).symm.trans hNonzeroFlag)
  | headLeft :: restLeft, headRight :: restRight, hLeftCanonical, hRightCanonical,
      hPointwise => by
      cases hHeads : grbExpBeq headLeft.exponentVector headRight.exponentVector with
      | true =>
          have headExpEq :=
            grbExpBeqEq headLeft.exponentVector headRight.exponentVector hHeads
          have hRightAtLeftExp : grqCoeff (headRight :: restRight)
              headLeft.exponentVector = headRight.coefficient := by
            rw [headExpEq]
            exact grqCoeffHeadIsCoefficient headRight restRight hRightCanonical
          have coeffEq : headLeft.coefficient = headRight.coefficient :=
            (grqCoeffHeadIsCoefficient headLeft restLeft hLeftCanonical).symm.trans
              ((hPointwise headLeft.exponentVector).trans hRightAtLeftExp)
          have headEq : headLeft = headRight :=
            (congrArg (fun value => GrqTerm.mk value headLeft.exponentVector) coeffEq).trans
              (congrArg (GrqTerm.mk headRight.coefficient) headExpEq)
          have tailsAgree : (probe : GrbExp) →
              grqCoeff restLeft probe = grqCoeff restRight probe := by
            intro probe
            cases hProbeHead : grbExpBeq probe headLeft.exponentVector with
            | true =>
                rw [grbExpBeqEq probe headLeft.exponentVector hProbeHead,
                  grqCoeffZeroUnderHead restLeft headLeft hLeftCanonical]
                have rightUnder : grqCoeff restRight headLeft.exponentVector = qnfZero := by
                  rw [headExpEq]
                  exact grqCoeffZeroUnderHead restRight headRight hRightCanonical
                exact rightUnder.symm
            | false =>
                have hProbeRight : grbExpBeq probe headRight.exponentVector = false := by
                  rw [← headExpEq]
                  exact hProbeHead
                have hPointAtExpanded :
                    qnfAdd (cond (grbExpBeq probe headLeft.exponentVector)
                        headLeft.coefficient qnfZero) (grqCoeff restLeft probe) =
                      qnfAdd (cond (grbExpBeq probe headRight.exponentVector)
                        headRight.coefficient qnfZero) (grqCoeff restRight probe) :=
                  hPointwise probe
                rw [hProbeHead, hProbeRight] at hPointAtExpanded
                exact (qnfAddZeroLeft (grqCoeff restLeft probe)).symm.trans
                  (hPointAtExpanded.trans (qnfAddZeroLeft (grqCoeff restRight probe)))
          rw [headEq]
          exact congrArg (List.cons headRight)
            (grqPolyExtensionality restLeft restRight
              (grqCanonicalTail headLeft restLeft hLeftCanonical)
              (grqCanonicalTail headRight restRight hRightCanonical) tailsAgree)
      | false =>
          exfalso
          have hLeftCoeffFlag := grqCanonicalHeadNonzero headLeft restLeft hLeftCanonical
          have hRightCoeffFlag :=
            grqCanonicalHeadNonzero headRight restRight hRightCanonical
          have hPointLeft :
              qnfAdd (cond (grbExpBeq headLeft.exponentVector headRight.exponentVector)
                  headRight.coefficient qnfZero)
                (grqCoeff restRight headLeft.exponentVector) = headLeft.coefficient :=
            (hPointwise headLeft.exponentVector).symm.trans
              (grqCoeffHeadIsCoefficient headLeft restLeft hLeftCanonical)
          rw [hHeads] at hPointLeft
          have hRightTailNonzero :
              grqCoeff restRight headLeft.exponentVector = qnfZero → False := by
            intro isZero
            rw [isZero] at hPointLeft
            have hCollapse : qnfZero = headLeft.coefficient :=
              (qnfAddZeroLeft qnfZero).symm.trans hPointLeft
            rw [← hCollapse] at hLeftCoeffFlag
            exact Bool.noConfusion ((qnfBeqSelfIsTrue qnfZero).symm.trans hLeftCoeffFlag)
          have hLeftLessRight :
              grbMonoLess headLeft.exponentVector headRight.exponentVector = true :=
            grqCoeffNonzeroImpliesLessThanHead restRight headRight
              headLeft.exponentVector hRightCanonical hRightTailNonzero
          have hHeadsSym :
              grbExpBeq headRight.exponentVector headLeft.exponentVector = false := by
            cases hBackward : grbExpBeq headRight.exponentVector headLeft.exponentVector with
            | false => rfl
            | true =>
                have backwardEq := grbExpBeqEq headRight.exponentVector
                  headLeft.exponentVector hBackward
                rw [backwardEq] at hHeads
                rw [grbExpBeqRefl headLeft.exponentVector] at hHeads
                exact Bool.noConfusion hHeads
          have hPointRight :
              qnfAdd (cond (grbExpBeq headRight.exponentVector headLeft.exponentVector)
                  headLeft.coefficient qnfZero)
                (grqCoeff restLeft headRight.exponentVector) = headRight.coefficient :=
            (hPointwise headRight.exponentVector).trans
              (grqCoeffHeadIsCoefficient headRight restRight hRightCanonical)
          rw [hHeadsSym] at hPointRight
          have hLeftTailNonzero :
              grqCoeff restLeft headRight.exponentVector = qnfZero → False := by
            intro isZero
            rw [isZero] at hPointRight
            have hCollapse : qnfZero = headRight.coefficient :=
              (qnfAddZeroLeft qnfZero).symm.trans hPointRight
            rw [← hCollapse] at hRightCoeffFlag
            exact Bool.noConfusion ((qnfBeqSelfIsTrue qnfZero).symm.trans hRightCoeffFlag)
          have hRightLessLeft :
              grbMonoLess headRight.exponentVector headLeft.exponentVector = true :=
            grqCoeffNonzeroImpliesLessThanHead restLeft headLeft
              headRight.exponentVector hLeftCanonical hLeftTailNonzero
          exact Bool.noConfusion
            ((grbMonoLessAsym headLeft.exponentVector headRight.exponentVector
              hLeftLessRight).symm.trans hRightLessLeft)

/-! ## The AC family the checker and finder consume — all one-fire extensionality -/

/-- `grqAdd poly [] = poly` on canonical input. -/
theorem grqAddNilRightIsIdentity (poly : GrqPoly) (hCanonical : GrqPolyCanonical poly) :
    grqAdd poly [] = poly :=
  grqPolyExtensionality (grqAdd poly []) poly
    (grqAddKeepsCanonical poly [] GrqPolyCanonical.nilIsCanonical) hCanonical
    (fun probe => by
      rw [grqCoeffAdd poly [] probe]
      exact qnfAddZeroRight (grqCoeff poly probe))

/-- Associativity of `grqAdd` (third operand canonical suffices). -/
theorem grqAddAssoc (firstPoly secondPoly thirdPoly : GrqPoly)
    (hThirdCanonical : GrqPolyCanonical thirdPoly) :
    grqAdd (grqAdd firstPoly secondPoly) thirdPoly =
      grqAdd firstPoly (grqAdd secondPoly thirdPoly) :=
  grqPolyExtensionality (grqAdd (grqAdd firstPoly secondPoly) thirdPoly)
    (grqAdd firstPoly (grqAdd secondPoly thirdPoly))
    (grqAddKeepsCanonical (grqAdd firstPoly secondPoly) thirdPoly hThirdCanonical)
    (grqAddKeepsCanonical firstPoly (grqAdd secondPoly thirdPoly)
      (grqAddKeepsCanonical secondPoly thirdPoly hThirdCanonical))
    (fun probe => by
      rw [grqCoeffAdd (grqAdd firstPoly secondPoly) thirdPoly probe,
        grqCoeffAdd firstPoly secondPoly probe,
        grqCoeffAdd firstPoly (grqAdd secondPoly thirdPoly) probe,
        grqCoeffAdd secondPoly thirdPoly probe]
      exact qnfAddAssoc (grqCoeff firstPoly probe) (grqCoeff secondPoly probe)
        (grqCoeff thirdPoly probe))

/-- Left-swap for `grqAdd` (innermost operand canonical suffices). -/
theorem grqAddSwapLeft (firstPoly secondPoly restPoly : GrqPoly)
    (hRestCanonical : GrqPolyCanonical restPoly) :
    grqAdd firstPoly (grqAdd secondPoly restPoly) =
      grqAdd secondPoly (grqAdd firstPoly restPoly) :=
  grqPolyExtensionality (grqAdd firstPoly (grqAdd secondPoly restPoly))
    (grqAdd secondPoly (grqAdd firstPoly restPoly))
    (grqAddKeepsCanonical firstPoly (grqAdd secondPoly restPoly)
      (grqAddKeepsCanonical secondPoly restPoly hRestCanonical))
    (grqAddKeepsCanonical secondPoly (grqAdd firstPoly restPoly)
      (grqAddKeepsCanonical firstPoly restPoly hRestCanonical))
    (fun probe => by
      rw [grqCoeffAdd firstPoly (grqAdd secondPoly restPoly) probe,
        grqCoeffAdd secondPoly restPoly probe,
        grqCoeffAdd secondPoly (grqAdd firstPoly restPoly) probe,
        grqCoeffAdd firstPoly restPoly probe]
      exact grqQnfAddSwapLeft (grqCoeff firstPoly probe) (grqCoeff secondPoly probe)
        (grqCoeff restPoly probe))

/-- Left negation cancellation: `(-s) + (s + r) = r` — the collision engine. -/
theorem grqAddNegSelfCancelLeft (sharedPoly restPoly : GrqPoly)
    (hRestCanonical : GrqPolyCanonical restPoly) :
    grqAdd (grqNeg sharedPoly) (grqAdd sharedPoly restPoly) = restPoly :=
  grqPolyExtensionality (grqAdd (grqNeg sharedPoly) (grqAdd sharedPoly restPoly))
    restPoly
    (grqAddKeepsCanonical (grqNeg sharedPoly) (grqAdd sharedPoly restPoly)
      (grqAddKeepsCanonical sharedPoly restPoly hRestCanonical))
    hRestCanonical
    (fun probe => by
      rw [grqCoeffAdd (grqNeg sharedPoly) (grqAdd sharedPoly restPoly) probe,
        grqCoeffNeg sharedPoly probe, grqCoeffAdd sharedPoly restPoly probe]
      exact ((qnfAddAssoc (qnfNeg (grqCoeff sharedPoly probe))
          (grqCoeff sharedPoly probe) (grqCoeff restPoly probe)).symm.trans
        (congrArg (fun value => qnfAdd value (grqCoeff restPoly probe))
          (qnfAddNegLeft (grqCoeff sharedPoly probe)))).trans
        (qnfAddZeroLeft (grqCoeff restPoly probe)))

/-- Negated cross-cancellation: `((-s) + p) + (s + r) = p + r` — the reduce-step
engine (the ℚ replacement for the F2 xor cross-cancel). -/
theorem grqAddNegCrossCancel (sharedPoly firstPoly restPoly : GrqPoly)
    (hRestCanonical : GrqPolyCanonical restPoly) :
    grqAdd (grqAdd (grqNeg sharedPoly) firstPoly) (grqAdd sharedPoly restPoly) =
      grqAdd firstPoly restPoly :=
  grqPolyExtensionality
    (grqAdd (grqAdd (grqNeg sharedPoly) firstPoly) (grqAdd sharedPoly restPoly))
    (grqAdd firstPoly restPoly)
    (grqAddKeepsCanonical (grqAdd (grqNeg sharedPoly) firstPoly)
      (grqAdd sharedPoly restPoly)
      (grqAddKeepsCanonical sharedPoly restPoly hRestCanonical))
    (grqAddKeepsCanonical firstPoly restPoly hRestCanonical)
    (fun probe => by
      rw [grqCoeffAdd (grqAdd (grqNeg sharedPoly) firstPoly)
          (grqAdd sharedPoly restPoly) probe,
        grqCoeffAdd (grqNeg sharedPoly) firstPoly probe, grqCoeffNeg sharedPoly probe,
        grqCoeffAdd sharedPoly restPoly probe, grqCoeffAdd firstPoly restPoly probe]
      exact (grqQnfAddExchange (qnfNeg (grqCoeff sharedPoly probe))
          (grqCoeff firstPoly probe) (grqCoeff sharedPoly probe)
          (grqCoeff restPoly probe)).trans
        ((congrArg (fun value => qnfAdd value
            (qnfAdd (grqCoeff firstPoly probe) (grqCoeff restPoly probe)))
          (qnfAddNegLeft (grqCoeff sharedPoly probe))).trans
          (qnfAddZeroLeft
            (qnfAdd (grqCoeff firstPoly probe) (grqCoeff restPoly probe)))))

/-- A zero-coefficient scaled polynomial is additively invisible. -/
theorem grqAddScaleTermZeroCoeffIsIdentity (gen tailPoly : GrqPoly) (monomial : GrbExp)
    (hTailCanonical : GrqPolyCanonical tailPoly) :
    grqAdd (grqScaleTerm qnfZero monomial gen) tailPoly = tailPoly :=
  grqPolyExtensionality (grqAdd (grqScaleTerm qnfZero monomial gen) tailPoly) tailPoly
    (grqAddKeepsCanonical (grqScaleTerm qnfZero monomial gen) tailPoly hTailCanonical)
    hTailCanonical
    (fun probe => by
      rw [grqCoeffAdd (grqScaleTerm qnfZero monomial gen) tailPoly probe,
        grqCoeffScaleTermZero gen monomial probe]
      exact qnfAddZeroLeft (grqCoeff tailPoly probe))

/-- A sum-coefficient scaled polynomial splits into two scaled summands. -/
theorem grqAddScaleTermSplitCoeff (gen tailPoly : GrqPoly)
    (leftScalar rightScalar : QnfRat) (monomial : GrbExp)
    (hTailCanonical : GrqPolyCanonical tailPoly) :
    grqAdd (grqScaleTerm (qnfAdd leftScalar rightScalar) monomial gen) tailPoly =
      grqAdd (grqScaleTerm leftScalar monomial gen)
        (grqAdd (grqScaleTerm rightScalar monomial gen) tailPoly) :=
  grqPolyExtensionality
    (grqAdd (grqScaleTerm (qnfAdd leftScalar rightScalar) monomial gen) tailPoly)
    (grqAdd (grqScaleTerm leftScalar monomial gen)
      (grqAdd (grqScaleTerm rightScalar monomial gen) tailPoly))
    (grqAddKeepsCanonical (grqScaleTerm (qnfAdd leftScalar rightScalar) monomial gen)
      tailPoly hTailCanonical)
    (grqAddKeepsCanonical (grqScaleTerm leftScalar monomial gen)
      (grqAdd (grqScaleTerm rightScalar monomial gen) tailPoly)
      (grqAddKeepsCanonical (grqScaleTerm rightScalar monomial gen) tailPoly
        hTailCanonical))
    (fun probe => by
      rw [grqCoeffAdd (grqScaleTerm (qnfAdd leftScalar rightScalar) monomial gen)
          tailPoly probe,
        grqCoeffScaleTermAddCoeff gen leftScalar rightScalar monomial probe,
        grqCoeffAdd (grqScaleTerm leftScalar monomial gen)
          (grqAdd (grqScaleTerm rightScalar monomial gen) tailPoly) probe,
        grqCoeffAdd (grqScaleTerm rightScalar monomial gen) tailPoly probe]
      exact qnfAddAssoc (grqCoeff (grqScaleTerm leftScalar monomial gen) probe)
        (grqCoeff (grqScaleTerm rightScalar monomial gen) probe)
        (grqCoeff tailPoly probe))

/-- Multiplication distributes over a term insertion — the cofactor-update law. -/
theorem grqMulTermInsert : (cofactor : GrqPoly) → (coefficient : QnfRat) →
    (exponent : GrbExp) → (gen : GrqPoly) →
    grqMul (grqTermInsert coefficient exponent cofactor) gen =
      grqAdd (grqScaleTerm coefficient exponent gen) (grqMul cofactor gen)
  | [], coefficient, exponent, gen => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertNilOnZeroCoefficient coefficient exponent hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero, grqMulNilLeft gen]
          exact (grqAddScaleTermZeroCoeffIsIdentity gen [] exponent
            GrqPolyCanonical.nilIsCanonical).symm
      | false =>
          rw [grqTermInsertNilOnNonzeroCoefficient coefficient exponent hZero]
          rfl
  | head :: rest, coefficient, exponent, gen => by
      cases hZero : qnfBeq coefficient qnfZero with
      | true =>
          rw [grqTermInsertOnZeroCoefficient coefficient exponent head rest hZero,
            (qnfBeqIffEq coefficient qnfZero).mp hZero]
          exact (grqAddScaleTermZeroCoeffIsIdentity gen (grqMul (head :: rest) gen)
            exponent (grqMulIsCanonical (head :: rest) gen)).symm
      | false =>
          cases hShared : grbExpBeq exponent head.exponentVector with
          | true =>
              have expEq := grbExpBeqEq exponent head.exponentVector hShared
              cases hSum : qnfBeq (qnfAdd coefficient head.coefficient) qnfZero with
              | true =>
                  rw [grqTermInsertOnCollisionCancel coefficient exponent head rest
                      hZero hShared hSum, expEq,
                    grqQnfEqNegOfAddEqZero
                      ((qnfBeqIffEq (qnfAdd coefficient head.coefficient) qnfZero).mp hSum),
                    grqScaleTermNegCoeff gen head.coefficient head.exponentVector]
                  exact (grqAddNegSelfCancelLeft
                    (grqScaleTerm head.coefficient head.exponentVector gen)
                    (grqMul rest gen) (grqMulIsCanonical rest gen)).symm
              | false =>
                  rw [grqTermInsertOnCollisionMerge coefficient exponent head rest
                    hZero hShared hSum, expEq]
                  show grqAdd (grqScaleTerm (qnfAdd coefficient head.coefficient)
                      head.exponentVector gen) (grqMul rest gen) =
                    grqAdd (grqScaleTerm coefficient head.exponentVector gen)
                      (grqAdd (grqScaleTerm head.coefficient head.exponentVector gen)
                        (grqMul rest gen))
                  exact grqAddScaleTermSplitCoeff gen (grqMul rest gen) coefficient
                    head.coefficient head.exponentVector (grqMulIsCanonical rest gen)
          | false =>
              cases hLess : grbMonoLess head.exponentVector exponent with
              | true =>
                  rw [grqTermInsertOnGreater coefficient exponent head rest
                    hZero hShared hLess]
                  rfl
              | false =>
                  rw [grqTermInsertOnSmaller coefficient exponent head rest
                    hZero hShared hLess]
                  show grqAdd (grqScaleTerm head.coefficient head.exponentVector gen)
                      (grqMul (grqTermInsert coefficient exponent rest) gen) =
                    grqAdd (grqScaleTerm coefficient exponent gen)
                      (grqAdd (grqScaleTerm head.coefficient head.exponentVector gen)
                        (grqMul rest gen))
                  rw [grqMulTermInsert rest coefficient exponent gen]
                  exact grqAddSwapLeft
                    (grqScaleTerm head.coefficient head.exponentVector gen)
                    (grqScaleTerm coefficient exponent gen) (grqMul rest gen)
                    (grqMulIsCanonical rest gen)

/-! ## THE CHECKER: semantic ideal membership + certificate soundness -/

/-- Bespoke list membership for generator lists. -/
inductive GrqMember : GrqPoly → List GrqPoly → Prop where
  | atHead (element : GrqPoly) (rest : List GrqPoly) : GrqMember element (element :: rest)
  | inTail (element head : GrqPoly) (rest : List GrqPoly)
      (isInRest : GrqMember element rest) : GrqMember element (head :: rest)

/-- **Semantic ideal membership**: the inductive closure of the generator list under
zero, addition, and scaling by ANY polynomial. -/
inductive GrqInIdeal (generators : List GrqPoly) : GrqPoly → Prop where
  | byZeroPolynomial : GrqInIdeal generators []
  | byGenerator (gen : GrqPoly) (isGenerator : GrqMember gen generators) :
      GrqInIdeal generators gen
  | byAddition (leftPoly rightPoly : GrqPoly)
      (leftInIdeal : GrqInIdeal generators leftPoly)
      (rightInIdeal : GrqInIdeal generators rightPoly) :
      GrqInIdeal generators (grqAdd leftPoly rightPoly)
  | byPolynomialScale (multiplier member : GrqPoly)
      (memberInIdeal : GrqInIdeal generators member) :
      GrqInIdeal generators (grqMul multiplier member)

/-- **THE CHECKER**: a certificate (cofactor list aligned with the generators)
checks when `Σ cofᵢ·genᵢ` is byte-equal to the target.  Pure polynomial
arithmetic over canonical rational coefficients — no search, no termination. -/
def grqCheckCertificate (generators cofactors : List GrqPoly) (target : GrqPoly) : Bool :=
  grqPolyBeq (grqSumOfProducts cofactors generators) target

/-- Every pairwise-product sum over a sublist of the generators is in the ideal. -/
theorem grqSumOfProductsInIdeal : (cofactors selected : List GrqPoly) →
    (generators : List GrqPoly) →
    ((gen : GrqPoly) → GrqMember gen selected → GrqMember gen generators) →
    GrqInIdeal generators (grqSumOfProducts cofactors selected)
  | [], [], _, _ => GrqInIdeal.byZeroPolynomial
  | [], _ :: _, _, _ => GrqInIdeal.byZeroPolynomial
  | _ :: _, [], _, _ => GrqInIdeal.byZeroPolynomial
  | cofactor :: cofactorRest, gen :: genRest, generators, hSubset =>
      GrqInIdeal.byAddition _ _
        (GrqInIdeal.byPolynomialScale cofactor gen
          (GrqInIdeal.byGenerator gen (hSubset gen (GrqMember.atHead gen genRest))))
        (grqSumOfProductsInIdeal cofactorRest genRest generators
          (fun element isMember =>
            hSubset element (GrqMember.inTail element gen genRest isMember)))

/-- **THE SOUNDNESS THEOREM**: an accepted certificate puts the target in the
ideal — no canonicity hypothesis on ANY input. -/
theorem grqCertificateSound (generators cofactors : List GrqPoly) (target : GrqPoly)
    (hCheckPasses : grqCheckCertificate generators cofactors target = true) :
    GrqInIdeal generators target :=
  grqPolyBeqEq (grqSumOfProducts cofactors generators) target hCheckPasses ▸
    grqSumOfProductsInIdeal cofactors generators generators (fun _ isMember => isMember)

/-! ## THE FINDER: fuel-bounded top-reduction with rational cofactor accumulation

Untrusted-but-verified-on-success.  THE STEP F2 GOT FOR FREE: the reducer scale is
`leadCoefficient · qnfInv(generatorLeadCoefficient)` — exact division by an
arbitrary nonzero rational leading coefficient.  Scale/quotient CORRECTNESS is
never needed by any theorem (it only affects progress); the invariant holds at
EVERY fuel level, so fuel exhaustion still leaves a checkable partial
certificate, and a run reaching remainder `[]` yields cofactors the checker
accepts (`grqFoundCertificateCertifies`). -/

/-- A reducer choice: which generator fires, with what rational scale and
quotient monomial. -/
structure GrqReducerChoice where
  cofactorIndex : Nat
  scaleCoefficient : QnfRat
  quotientExponent : GrbExp
  reducerBody : GrqPoly

/-- Shift a reducer choice one generator to the right. -/
def grqBumpReducerIndex : Option GrqReducerChoice → Option GrqReducerChoice
  | none => none
  | some found => some { found with cofactorIndex := Nat.succ found.cofactorIndex }

/-- Scan the generators for the first whose leading exponent divides the lead
(zero generators are skipped); the scale is the lead coefficient divided by the
generator's lead coefficient via `qnfInv` — the rational division step. -/
def grqFindReducer : List GrqPoly → QnfRat → GrbExp → Option GrqReducerChoice
  | [], _, _ => none
  | [] :: rest, leadCoefficient, leadExponent =>
      grqBumpReducerIndex (grqFindReducer rest leadCoefficient leadExponent)
  | (genHead :: genRest) :: rest, leadCoefficient, leadExponent =>
      cond (grbExpDivides genHead.exponentVector leadExponent)
        (some { cofactorIndex := 0,
                scaleCoefficient := qnfMul leadCoefficient (qnfInv genHead.coefficient),
                quotientExponent := grbExpQuotient leadExponent genHead.exponentVector,
                reducerBody := genHead :: genRest })
        (grqBumpReducerIndex (grqFindReducer rest leadCoefficient leadExponent))

/-- Positional generator lookup. -/
def grqGeneratorAt : List GrqPoly → Nat → Option GrqPoly
  | [], 0 => none
  | [], Nat.succ _ => none
  | gen :: _, 0 => some gen
  | _ :: rest, Nat.succ index => grqGeneratorAt rest index

/-- A found reducer really is the generator at its index. -/
theorem grqFindReducerPointsAtGenerator : (generators : List GrqPoly) →
    (leadCoefficient : QnfRat) → (leadExponent : GrbExp) → (choice : GrqReducerChoice) →
    grqFindReducer generators leadCoefficient leadExponent = some choice →
    grqGeneratorAt generators choice.cofactorIndex = some choice.reducerBody
  | [], _, _, choice, hFind => by
      have hImpossible : (none : Option GrqReducerChoice) = some choice := hFind
      exact nomatch hImpossible
  | [] :: rest, leadCoefficient, leadExponent, choice, hFind => by
      have hFindFull : grqBumpReducerIndex
          (grqFindReducer rest leadCoefficient leadExponent) = some choice := hFind
      cases hInner : grqFindReducer rest leadCoefficient leadExponent with
      | none =>
          rw [hInner] at hFindFull
          have hImpossible : (none : Option GrqReducerChoice) = some choice := hFindFull
          exact nomatch hImpossible
      | some inner =>
          rw [hInner] at hFindFull
          have choiceEq := Option.some.inj hFindFull
          rw [← choiceEq]
          exact grqFindReducerPointsAtGenerator rest leadCoefficient leadExponent
            inner hInner
  | (genHead :: genRest) :: rest, leadCoefficient, leadExponent, choice, hFind => by
      have hFindFull : cond (grbExpDivides genHead.exponentVector leadExponent)
          (some { cofactorIndex := 0,
                  scaleCoefficient := qnfMul leadCoefficient (qnfInv genHead.coefficient),
                  quotientExponent := grbExpQuotient leadExponent genHead.exponentVector,
                  reducerBody := genHead :: genRest })
          (grqBumpReducerIndex (grqFindReducer rest leadCoefficient leadExponent)) =
          some choice := hFind
      cases hDivides : grbExpDivides genHead.exponentVector leadExponent with
      | true =>
          rw [hDivides] at hFindFull
          have choiceEq := Option.some.inj hFindFull
          rw [← choiceEq]
          rfl
      | false =>
          rw [hDivides] at hFindFull
          cases hInner : grqFindReducer rest leadCoefficient leadExponent with
          | none =>
              rw [hInner] at hFindFull
              have hImpossible : (none : Option GrqReducerChoice) = some choice :=
                hFindFull
              exact nomatch hImpossible
          | some inner =>
              rw [hInner] at hFindFull
              have choiceEq := Option.some.inj hFindFull
              rw [← choiceEq]
              exact grqFindReducerPointsAtGenerator rest leadCoefficient leadExponent
                inner hInner

/-- Length agreement between a cofactor list and the generator list. -/
def grqHasSameLength : List GrqPoly → List GrqPoly → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | _ :: leftRest, _ :: rightRest => grqHasSameLength leftRest rightRest

/-- Insert a scaled term into the cofactor at the given index. -/
def grqUpdateCofactors : Nat → QnfRat → GrbExp → List GrqPoly → List GrqPoly
  | 0, _, _, [] => []
  | 0, scalar, monomial, cofactor :: rest =>
      grqTermInsert scalar monomial cofactor :: rest
  | Nat.succ _, _, _, [] => []
  | Nat.succ index, scalar, monomial, cofactor :: rest =>
      cofactor :: grqUpdateCofactors index scalar monomial rest

/-- Cofactor update preserves length agreement. -/
theorem grqUpdateCofactorsKeepLength : (cofactors generators : List GrqPoly) →
    (index : Nat) → (scalar : QnfRat) → (monomial : GrbExp) →
    grqHasSameLength cofactors generators = true →
    grqHasSameLength (grqUpdateCofactors index scalar monomial cofactors) generators = true
  | [], _, 0, _, _, hLengths => hLengths
  | [], _, Nat.succ _, _, _, hLengths => hLengths
  | _ :: _, [], 0, _, _, hLengths => Bool.noConfusion hLengths
  | _ :: _, [], Nat.succ _, _, _, hLengths => Bool.noConfusion hLengths
  | _ :: _, _ :: _, 0, _, _, hLengths => hLengths
  | _ :: cofactorRest, _ :: genRest, Nat.succ index, scalar, monomial, hLengths =>
      grqUpdateCofactorsKeepLength cofactorRest genRest index scalar monomial hLengths

/-- Updating cofactor `i` by the scaled term shifts the product sum by
`scalar·monomial · genᵢ`. -/
theorem grqSumUpdateCofactors : (cofactors generators : List GrqPoly) → (index : Nat) →
    (scalar : QnfRat) → (monomial : GrbExp) → (gen : GrqPoly) →
    grqHasSameLength cofactors generators = true →
    grqGeneratorAt generators index = some gen →
    grqSumOfProducts (grqUpdateCofactors index scalar monomial cofactors) generators =
      grqAdd (grqScaleTerm scalar monomial gen) (grqSumOfProducts cofactors generators)
  | [], [], 0, _, _, gen, _, hGeneratorHit => by
      have hImpossible : (none : Option GrqPoly) = some gen := hGeneratorHit
      exact nomatch hImpossible
  | [], [], Nat.succ _, _, _, gen, _, hGeneratorHit => by
      have hImpossible : (none : Option GrqPoly) = some gen := hGeneratorHit
      exact nomatch hImpossible
  | [], _ :: _, _, _, _, _, hLengths, _ => Bool.noConfusion hLengths
  | _ :: _, [], _, _, _, _, hLengths, _ => Bool.noConfusion hLengths
  | cofactor :: cofactorRest, genHead :: genRest, 0, scalar, monomial, gen, _,
      hGeneratorHit => by
      have genEq : genHead = gen := Option.some.inj hGeneratorHit
      subst genEq
      show grqAdd (grqMul (grqTermInsert scalar monomial cofactor) genHead)
        (grqSumOfProducts cofactorRest genRest) = _
      rw [grqMulTermInsert cofactor scalar monomial genHead]
      exact grqAddAssoc (grqScaleTerm scalar monomial genHead) (grqMul cofactor genHead)
        (grqSumOfProducts cofactorRest genRest)
        (grqSumOfProductsIsCanonical cofactorRest genRest)
  | cofactor :: cofactorRest, genHead :: genRest, Nat.succ index, scalar, monomial, gen,
      hLengths, hGeneratorHit => by
      show grqAdd (grqMul cofactor genHead)
        (grqSumOfProducts (grqUpdateCofactors index scalar monomial cofactorRest)
          genRest) = _
      rw [grqSumUpdateCofactors cofactorRest genRest index scalar monomial gen hLengths
        hGeneratorHit]
      exact grqAddSwapLeft (grqMul cofactor genHead) (grqScaleTerm scalar monomial gen)
        (grqSumOfProducts cofactorRest genRest)
        (grqSumOfProductsIsCanonical cofactorRest genRest)

/-- The reduce result: the working remainder and the accumulated cofactors. -/
structure GrqReduceResult where
  remainderPoly : GrqPoly
  cofactorPolys : List GrqPoly

/-- Package a fired reducer choice into the next reduce state: the remainder
SUBTRACTS the scaled generator (negation plus insert-fold addition), the matching
cofactor absorbs the scaled term. -/
def grqApplyReducerChoice (leadTerm : GrqTerm) (restPoly : GrqPoly)
    (cofactors : List GrqPoly) : Option GrqReducerChoice → Option GrqReduceResult
  | none => none
  | some choice =>
      some { remainderPoly :=
               grqAdd (grqNeg (grqScaleTerm choice.scaleCoefficient
                 choice.quotientExponent choice.reducerBody))
                 (leadTerm :: restPoly),
             cofactorPolys :=
               grqUpdateCofactors choice.cofactorIndex choice.scaleCoefficient
                 choice.quotientExponent cofactors }

/-- **One top-reduction step**: subtract `scale·quotient · genᵢ` where `scale` is
the rational lead-coefficient ratio and `quotient` the exact exponent quotient,
and record the scaled term in cofactor `i`.  Returns `none` when the polynomial is
zero or no generator's lead divides. -/
def grqReduceStep (generators : List GrqPoly) (poly : GrqPoly)
    (cofactors : List GrqPoly) : Option GrqReduceResult :=
  match poly with
  | [] => none
  | leadTerm :: restPoly =>
      grqApplyReducerChoice leadTerm restPoly cofactors
        (grqFindReducer generators leadTerm.coefficient leadTerm.exponentVector)

/-- **The fuel-bounded finder loop** (structural on fuel — no `WellFounded.fix`). -/
def grqReduce : Nat → List GrqPoly → GrqPoly → List GrqPoly → GrqReduceResult
  | 0, _, poly, cofactors => { remainderPoly := poly, cofactorPolys := cofactors }
  | Nat.succ fuel, generators, poly, cofactors =>
      match grqReduceStep generators poly cofactors with
      | none => { remainderPoly := poly, cofactorPolys := cofactors }
      | some stepResult =>
          grqReduce fuel generators stepResult.remainderPoly stepResult.cofactorPolys

/-- A fired step preserves lengths and the running certificate sum. -/
theorem grqReduceStepPreservesSum (generators : List GrqPoly) (poly : GrqPoly)
    (cofactors : List GrqPoly) (next : GrqReduceResult)
    (hLengths : grqHasSameLength cofactors generators = true)
    (hStepFires : grqReduceStep generators poly cofactors = some next) :
    grqHasSameLength next.cofactorPolys generators = true ∧
      grqAdd next.remainderPoly (grqSumOfProducts next.cofactorPolys generators) =
        grqAdd poly (grqSumOfProducts cofactors generators) := by
  cases poly with
  | nil =>
      have hImpossible : (none : Option GrqReduceResult) = some next := hStepFires
      exact nomatch hImpossible
  | cons leadTerm restPoly =>
      have hStepFull : grqApplyReducerChoice leadTerm restPoly cofactors
          (grqFindReducer generators leadTerm.coefficient leadTerm.exponentVector) =
          some next := hStepFires
      cases hFind : grqFindReducer generators leadTerm.coefficient
          leadTerm.exponentVector with
      | none =>
          rw [hFind] at hStepFull
          have hImpossible : (none : Option GrqReduceResult) = some next := hStepFull
          exact nomatch hImpossible
      | some choice =>
          rw [hFind] at hStepFull
          have nextEq := Option.some.inj hStepFull
          rw [← nextEq]
          constructor
          · exact grqUpdateCofactorsKeepLength cofactors generators choice.cofactorIndex
              choice.scaleCoefficient choice.quotientExponent hLengths
          · show grqAdd
                (grqAdd (grqNeg (grqScaleTerm choice.scaleCoefficient
                  choice.quotientExponent choice.reducerBody)) (leadTerm :: restPoly))
                (grqSumOfProducts
                  (grqUpdateCofactors choice.cofactorIndex choice.scaleCoefficient
                    choice.quotientExponent cofactors) generators) =
              grqAdd (leadTerm :: restPoly) (grqSumOfProducts cofactors generators)
            rw [grqSumUpdateCofactors cofactors generators choice.cofactorIndex
              choice.scaleCoefficient choice.quotientExponent choice.reducerBody hLengths
              (grqFindReducerPointsAtGenerator generators leadTerm.coefficient
                leadTerm.exponentVector choice hFind)]
            exact grqAddNegCrossCancel
              (grqScaleTerm choice.scaleCoefficient choice.quotientExponent
                choice.reducerBody)
              (leadTerm :: restPoly) (grqSumOfProducts cofactors generators)
              (grqSumOfProductsIsCanonical cofactors generators)

/-- Reduce unfolding: a stuck step returns the state unchanged. -/
theorem grqReduceOnStuckStep (fuel : Nat) (generators : List GrqPoly) (poly : GrqPoly)
    (cofactors : List GrqPoly)
    (hStepStuck : grqReduceStep generators poly cofactors = none) :
    grqReduce (Nat.succ fuel) generators poly cofactors =
      { remainderPoly := poly, cofactorPolys := cofactors } := by
  show (match grqReduceStep generators poly cofactors with
    | none => ({ remainderPoly := poly, cofactorPolys := cofactors } : GrqReduceResult)
    | some stepResult =>
        grqReduce fuel generators stepResult.remainderPoly stepResult.cofactorPolys) =
    { remainderPoly := poly, cofactorPolys := cofactors }
  rw [hStepStuck]

/-- Reduce unfolding: a fired step recurses on the stepped state. -/
theorem grqReduceOnFiringStep (fuel : Nat) (generators : List GrqPoly) (poly : GrqPoly)
    (cofactors : List GrqPoly) (next : GrqReduceResult)
    (hStepFires : grqReduceStep generators poly cofactors = some next) :
    grqReduce (Nat.succ fuel) generators poly cofactors =
      grqReduce fuel generators next.remainderPoly next.cofactorPolys := by
  show (match grqReduceStep generators poly cofactors with
    | none => ({ remainderPoly := poly, cofactorPolys := cofactors } : GrqReduceResult)
    | some stepResult =>
        grqReduce fuel generators stepResult.remainderPoly stepResult.cofactorPolys) =
    grqReduce fuel generators next.remainderPoly next.cofactorPolys
  rw [hStepFires]

/-- **THE REDUCE INVARIANT**: at every fuel level, `remainder + Σ cofᵢ·genᵢ` equals
the input `poly + Σ cof⁰ᵢ·genᵢ` as canonical lists — fuel exhaustion still leaves a
checkable partial certificate. -/
theorem grqReduceInvariant : (fuel : Nat) → (generators : List GrqPoly) →
    (poly : GrqPoly) → (cofactors : List GrqPoly) →
    grqHasSameLength cofactors generators = true →
    grqHasSameLength (grqReduce fuel generators poly cofactors).cofactorPolys
        generators = true ∧
      grqAdd (grqReduce fuel generators poly cofactors).remainderPoly
          (grqSumOfProducts (grqReduce fuel generators poly cofactors).cofactorPolys
            generators) =
        grqAdd poly (grqSumOfProducts cofactors generators)
  | 0, _, _, _, hLengths => ⟨hLengths, rfl⟩
  | Nat.succ fuel, generators, poly, cofactors, hLengths => by
      cases hStep : grqReduceStep generators poly cofactors with
      | none =>
          rw [grqReduceOnStuckStep fuel generators poly cofactors hStep]
          exact ⟨hLengths, rfl⟩
      | some next =>
          rw [grqReduceOnFiringStep fuel generators poly cofactors next hStep]
          have hStepFacts := grqReduceStepPreservesSum generators poly cofactors next
            hLengths hStep
          have hRecursiveFacts := grqReduceInvariant fuel generators next.remainderPoly
            next.cofactorPolys hStepFacts.left
          exact ⟨hRecursiveFacts.left, hRecursiveFacts.right.trans hStepFacts.right⟩

/-- The all-zero cofactor seed aligned with the generator list. -/
def grqZeroCofactorsFor : List GrqPoly → List GrqPoly
  | [] => []
  | _ :: rest => [] :: grqZeroCofactorsFor rest

/-- The zero seed agrees in length with the generators. -/
theorem grqZeroCofactorsMatchLength : (generators : List GrqPoly) →
    grqHasSameLength (grqZeroCofactorsFor generators) generators = true
  | [] => rfl
  | _ :: rest => grqZeroCofactorsMatchLength rest

/-- The zero seed's product sum is the zero polynomial. -/
theorem grqSumOfZeroCofactorsIsNil : (generators : List GrqPoly) →
    grqSumOfProducts (grqZeroCofactorsFor generators) generators = []
  | [] => rfl
  | gen :: rest => by
      show grqAdd (grqMul [] gen) (grqSumOfProducts (grqZeroCofactorsFor rest) rest) = []
      rw [grqMulNilLeft gen]
      show grqSumOfProducts (grqZeroCofactorsFor rest) rest = []
      exact grqSumOfZeroCofactorsIsNil rest

/-- **FINDER SELF-CERTIFICATION**: a run from the zero seed that reaches remainder
`[]` yields cofactors the checker accepts — finder success always produces a valid
certificate, including through every rational-division step. -/
theorem grqFoundCertificateCertifies (fuel : Nat) (generators : List GrqPoly)
    (target : GrqPoly) (hTargetCanonical : GrqPolyCanonical target)
    (hRemainderVanishes :
      (grqReduce fuel generators target (grqZeroCofactorsFor generators)).remainderPoly =
        []) :
    grqCheckCertificate generators
      (grqReduce fuel generators target (grqZeroCofactorsFor generators)).cofactorPolys
      target = true := by
  have hInvariant := grqReduceInvariant fuel generators target
    (grqZeroCofactorsFor generators) (grqZeroCofactorsMatchLength generators)
  have hSumEquation := hInvariant.right
  rw [hRemainderVanishes, grqSumOfZeroCofactorsIsNil generators,
    grqAddNilRightIsIdentity target hTargetCanonical] at hSumEquation
  have hSumIsTarget : grqSumOfProducts
      (grqReduce fuel generators target (grqZeroCofactorsFor generators)).cofactorPolys
      generators = target := hSumEquation
  show grqPolyBeq (grqSumOfProducts
    (grqReduce fuel generators target (grqZeroCofactorsFor generators)).cofactorPolys
    generators) target = true
  rw [hSumIsTarget]
  exact grqPolyBeqRefl target

/-! ## Kernel `rfl` fires (small magnitudes; the counting divider is
unary-recursive, so numerators/denominators stay tiny) -/

set_option maxRecDepth 8192

/-- Fire fixture: `x^2 - 1` (variable 0). -/
def grqFireXSquaredMinusOne : GrqPoly :=
  [{ coefficient := qnfOne,
     exponentVector := [{ variableIndex := 0, exponent := 2 }] },
   { coefficient := qnfNeg qnfOne, exponentVector := [] }]

/-- Fire fixture: `x - 1`. -/
def grqFireXMinusOne : GrqPoly :=
  [{ coefficient := qnfOne,
     exponentVector := [{ variableIndex := 0, exponent := 1 }] },
   { coefficient := qnfNeg qnfOne, exponentVector := [] }]

/-- Fire fixture: `x + 1` — the hand cofactor for fire (a). -/
def grqFireXPlusOne : GrqPoly :=
  [{ coefficient := qnfOne,
     exponentVector := [{ variableIndex := 0, exponent := 1 }] },
   { coefficient := qnfOne, exponentVector := [] }]

/-- Fire (a), checker route: `x^2 - 1 ∈ ⟨x - 1⟩` with hand cofactor `x + 1`. -/
theorem grqFireCheckerAcceptsSquareCertificate :
    grqCheckCertificate [grqFireXMinusOne] [grqFireXPlusOne]
      grqFireXSquaredMinusOne = true := rfl

/-- Fire (a), finder route: the reduction reaches remainder `[]`. -/
theorem grqFireFinderReducesSquare :
    (grqReduce 8 [grqFireXMinusOne] grqFireXSquaredMinusOne
      (grqZeroCofactorsFor [grqFireXMinusOne])).remainderPoly = [] := rfl

/-- Fire (a), finder route: the found certificate checks. -/
theorem grqFireFinderCertificateChecksSquare :
    grqCheckCertificate [grqFireXMinusOne]
      (grqReduce 8 [grqFireXMinusOne] grqFireXSquaredMinusOne
        (grqZeroCofactorsFor [grqFireXMinusOne])).cofactorPolys
      grqFireXSquaredMinusOne = true := rfl

/-- Fire fixture: the canonical `2/3`. -/
def grqFireTwoThirds : QnfRat :=
  qnfNormalize { numerator := 2, denominatorPredecessor := 2 }

/-- Fire fixture: `2x`. -/
def grqFireTwoTimesX : GrqPoly :=
  [{ coefficient := qnfOfInt 2,
     exponentVector := [{ variableIndex := 0, exponent := 1 }] }]

/-- Fire fixture: `3x`. -/
def grqFireThreeTimesX : GrqPoly :=
  [{ coefficient := qnfOfInt 3,
     exponentVector := [{ variableIndex := 0, exponent := 1 }] }]

/-- Fire fixture: the constant polynomial `2/3`. -/
def grqFireTwoThirdsConstant : GrqPoly :=
  [{ coefficient := grqFireTwoThirds, exponentVector := [] }]

/-- **Fire (b) — THE ℚ-vs-ℤ SEPARATOR, checker route**: `2x ∈ ⟨3x⟩` via the
rational cofactor `2/3`.  Over ℤ no cofactor exists (`3q = 2` has no integer
solution); the content the rational coefficient field adds is exactly this fire. -/
theorem grqFireCheckerAcceptsRationalCofactor :
    grqCheckCertificate [grqFireThreeTimesX] [grqFireTwoThirdsConstant]
      grqFireTwoTimesX = true := rfl

/-- Fire (b), finder route: the reduction reaches remainder `[]` — the reducer
scale `2 · (3)⁻¹` is computed by `qnfInv`. -/
theorem grqFireFinderReducesRationalTarget :
    (grqReduce 4 [grqFireThreeTimesX] grqFireTwoTimesX
      (grqZeroCofactorsFor [grqFireThreeTimesX])).remainderPoly = [] := rfl

/-- Fire (b), finder route: the finder EMITS the canonical `2/3` cofactor —
byte-equal to the normalized fixture, pinning the rational division step. -/
theorem grqFireFinderEmitsRationalCofactor :
    (grqReduce 4 [grqFireThreeTimesX] grqFireTwoTimesX
      (grqZeroCofactorsFor [grqFireThreeTimesX])).cofactorPolys =
      [[{ coefficient := grqFireTwoThirds, exponentVector := [] }]] := rfl

/-- Fire fixture: `x·y - 1` (variables 0 and 1). -/
def grqFireXTimesYMinusOne : GrqPoly :=
  [{ coefficient := qnfOne,
     exponentVector := [{ variableIndex := 0, exponent := 1 },
                        { variableIndex := 1, exponent := 1 }] },
   { coefficient := qnfNeg qnfOne, exponentVector := [] }]

/-- Fire fixture: `y - 1`. -/
def grqFireYMinusOne : GrqPoly :=
  [{ coefficient := qnfOne,
     exponentVector := [{ variableIndex := 1, exponent := 1 }] },
   { coefficient := qnfNeg qnfOne, exponentVector := [] }]

/-- Fire (c), checker route: `x·y - 1 ∈ ⟨x - 1, y - 1⟩` with hand cofactors
`(y, 1)`. -/
theorem grqFireCheckerAcceptsTwoVariableCertificate :
    grqCheckCertificate [grqFireXMinusOne, grqFireYMinusOne]
      [grqVariablePoly 1, grqOnePoly] grqFireXTimesYMinusOne = true := rfl

/-- Fire (c), finder route: two reduction steps against two generators reach
remainder `[]`. -/
theorem grqFireFinderReducesTwoVariableTarget :
    (grqReduce 8 [grqFireXMinusOne, grqFireYMinusOne] grqFireXTimesYMinusOne
      (grqZeroCofactorsFor [grqFireXMinusOne, grqFireYMinusOne])).remainderPoly =
      [] := rfl

/-- Fire (c), finder route: the found two-cofactor certificate checks. -/
theorem grqFireFinderCertificateChecksTwoVariable :
    grqCheckCertificate [grqFireXMinusOne, grqFireYMinusOne]
      (grqReduce 8 [grqFireXMinusOne, grqFireYMinusOne] grqFireXTimesYMinusOne
        (grqZeroCofactorsFor [grqFireXMinusOne, grqFireYMinusOne])).cofactorPolys
      grqFireXTimesYMinusOne = true := rfl

/-- Fire (d), negative control: the constant `1` is NOT reducible by `⟨x⟩` — the
finder gets stuck and returns the remainder `1` unchanged. -/
theorem grqFireFinderStuckOnConstantOne :
    (grqReduce 8 [grqVariablePoly 0] grqOnePoly
      (grqZeroCofactorsFor [grqVariablePoly 0])).remainderPoly = grqOnePoly := rfl

/-- Fire (d), negative control: the bogus certificate `1·x` for the constant `1`
is REJECTED by the checker. -/
theorem grqFireCheckerRejectsBogusConstantCertificate :
    grqCheckCertificate [grqVariablePoly 0] [grqOnePoly] grqOnePoly = false := rfl

/-! ## Content markers -/

/-- DECIDED: the rational-coefficient certificate checker route — canonical
`QnfRat`-coefficient polynomial substrate, canonical-list extensionality
(`grqPolyExtensionality`), THE CHECKER (`grqCheckCertificate`) with
`grqCertificateSound` into the semantic inductive `GrqInIdeal`. -/
def grqHasRationalCertificateChecker : Bool := true

/-- DECIDED: the finder is self-certifying — fuel-bounded reduction with rational
division by leading coefficients (`qnfInv`), THE REDUCE INVARIANT
(`grqReduceInvariant`) at every fuel level, and `grqFoundCertificateCertifies` on
remainder `[]`.  Non-membership stays honestly out of scope: see the F2 wall
`grbNonMembershipDecisionStatement` / `fxDissatGrob_hasNonMembershipDecision`. -/
def grqHasSelfCertifyingFinder : Bool := true

end FX1Poly.ComputerAlgebra
