import FX1Poly.ComputerAlgebra.Number.NormalizedRational

/-! # Finite-groupoid cardinality as decategorification

The groupoid cardinality of Baez and Dolan: a finite groupoid, presented by its
skeleton as one automorphism-group order per isomorphism class, has cardinality
`Sum 1/|Aut(x)|`, an exact rational.  As a decategorified invariant it carries
the two structural laws of a rig homomorphism:

  * disjoint union is addition, `card (G + H) = card G + card H`;
  * cartesian product is multiplication, `card (G x H) = card G * card H`,

the product law resting on reciprocal multiplicativity `1/(a*b) = (1/a)*(1/b)`,
mirroring the automorphism group of a product being the product of automorphism
groups.

The carrier is a `List Nat` of automorphism-group orders over the canonical-NF
rational type `QnfRat`; cardinality is a cons-only `qnfAdd` fold of reciprocals
`qnfInv (qnfOfInt (Int.ofNat order))`.  Addition is an append-splits-sum
induction; multiplication adds reciprocal multiplicativity, proved from
field-law inverse uniqueness and the natural-number-to-rational multiplicative
homomorphism.

`fgcInverseAmbiguityWitness` places the point `[1]` and the two-object groupoid
`[2,2]` (each object of automorphism order two) at the common cardinality `1`,
so decategorification is not injective.  Three extensions recorded false by
`fgcHasGroupoidExtensions` lie outside this finite model: inverse
categorification (no map from a rational back to a groupoid), infinite-groupoid
cardinality (a convergent real series such as `Sum 1/n! = e` the finite fold
cannot complete), and equivalence of groupoids given by raw generators and
relations (graph-isomorphism-hard, automorphism-order extraction an orbit
problem); equivalence of the skeleton-list representation stays decidable by
sorting and comparing orders.

Zero-axiom: structural recursion on `List` and `Nat`, full-enumeration
constructor matches, `QnfRat` kernel arithmetic with its field-law suite, and
`calc`, `congrArg`, and `Eq.trans` reasoning.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`, `funext`, or `decide` on
`Prop`.  Gated per declaration in the audit twin. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Scalar `QnfRat` field-law lemmas

Multiplicative zero, the middle-four exchange, inverse uniqueness,
product-nonzero, inverse distributivity, and the integer and natural-number
multiplicative homomorphisms, all derived from the `QnfRat` field-law suite. -/

/-- `factor * 0 = 0` — from left distributivity and additive cancellation. -/
theorem fgcMulZeroRight (factor : QnfRat) : qnfMul factor qnfZero = qnfZero := by
  have hself : qnfMul factor qnfZero
      = qnfAdd (qnfMul factor qnfZero) (qnfMul factor qnfZero) := by
    have hdist := qnfMulLeftDistrib factor qnfZero qnfZero
    rw [qnfAddZeroRight qnfZero] at hdist
    exact hdist
  calc qnfMul factor qnfZero
      = qnfAdd (qnfMul factor qnfZero) qnfZero := (qnfAddZeroRight _).symm
    _ = qnfAdd (qnfMul factor qnfZero)
          (qnfAdd (qnfMul factor qnfZero) (qnfNeg (qnfMul factor qnfZero))) := by
            rw [qnfAddNegRight]
    _ = qnfAdd (qnfAdd (qnfMul factor qnfZero) (qnfMul factor qnfZero))
          (qnfNeg (qnfMul factor qnfZero)) := (qnfAddAssoc _ _ _).symm
    _ = qnfAdd (qnfMul factor qnfZero) (qnfNeg (qnfMul factor qnfZero)) := by
          rw [← hself]
    _ = qnfZero := qnfAddNegRight _

/-- `0 * factor = 0` — commute and reuse. -/
theorem fgcMulZeroLeft (factor : QnfRat) : qnfMul qnfZero factor = qnfZero :=
  (qnfMulComm qnfZero factor).trans (fgcMulZeroRight factor)

/-- Multiplicative middle-four exchange `(a*b)*(c*d) = (a*c)*(b*d)`, from
commutativity and associativity. -/
theorem fgcMulMiddleFour (firstFactor secondFactor thirdFactor fourthFactor : QnfRat) :
    qnfMul (qnfMul firstFactor secondFactor) (qnfMul thirdFactor fourthFactor) =
      qnfMul (qnfMul firstFactor thirdFactor) (qnfMul secondFactor fourthFactor) := by
  rw [qnfMulAssoc firstFactor secondFactor (qnfMul thirdFactor fourthFactor),
    ← qnfMulAssoc secondFactor thirdFactor fourthFactor,
    qnfMulComm secondFactor thirdFactor,
    qnfMulAssoc thirdFactor secondFactor fourthFactor,
    ← qnfMulAssoc firstFactor thirdFactor (qnfMul secondFactor fourthFactor)]

/-- Inverse uniqueness: a nonzero value's right inverse equals `qnfInv base`. -/
theorem fgcInverseUnique {base other : QnfRat} (baseNonzero : base ≠ qnfZero)
    (isInverse : qnfMul base other = qnfOne) : other = qnfInv base := by
  calc other = qnfMul qnfOne other := (qnfMulOneLeft other).symm
    _ = qnfMul (qnfMul (qnfInv base) base) other := by rw [qnfInvMulCancels baseNonzero]
    _ = qnfMul (qnfInv base) (qnfMul base other) := qnfMulAssoc _ _ _
    _ = qnfMul (qnfInv base) qnfOne := by rw [isInverse]
    _ = qnfInv base := qnfMulOneRight _

/-- A product of nonzero values is nonzero, by cancelling the left factor
against a hypothetical zero product. -/
theorem fgcMulNeZero {leftFactor rightFactor : QnfRat}
    (leftNonzero : leftFactor ≠ qnfZero) (rightNonzero : rightFactor ≠ qnfZero) :
    qnfMul leftFactor rightFactor ≠ qnfZero := by
  intro isZero
  apply rightNonzero
  calc rightFactor = qnfMul qnfOne rightFactor := (qnfMulOneLeft rightFactor).symm
    _ = qnfMul (qnfMul (qnfInv leftFactor) leftFactor) rightFactor := by
          rw [qnfInvMulCancels leftNonzero]
    _ = qnfMul (qnfInv leftFactor) (qnfMul leftFactor rightFactor) := qnfMulAssoc _ _ _
    _ = qnfMul (qnfInv leftFactor) qnfZero := by rw [isZero]
    _ = qnfZero := fgcMulZeroRight _

/-- Inverse distributes over multiplication on nonzero factors,
`(x*y) inverse = (x inverse)*(y inverse)`: the candidate is a right inverse of
`x*y` by the middle-four exchange, then pinned by inverse uniqueness. -/
theorem fgcInvMulDistrib {leftFactor rightFactor : QnfRat}
    (leftNonzero : leftFactor ≠ qnfZero) (rightNonzero : rightFactor ≠ qnfZero) :
    qnfInv (qnfMul leftFactor rightFactor) =
      qnfMul (qnfInv leftFactor) (qnfInv rightFactor) := by
  have prodInverse :
      qnfMul (qnfMul leftFactor rightFactor)
          (qnfMul (qnfInv leftFactor) (qnfInv rightFactor)) = qnfOne := by
    rw [fgcMulMiddleFour leftFactor rightFactor (qnfInv leftFactor) (qnfInv rightFactor),
      qnfMulInvCancels leftNonzero, qnfMulInvCancels rightNonzero, qnfMulOneRight]
  exact (fgcInverseUnique (fgcMulNeZero leftNonzero rightNonzero) prodInverse).symm

/-- The integer-to-rational multiplicative homomorphism
`(a/1)*(b/1) = (a*b)/1`: the product of canonical integer embeddings is the
embedding of their product, fixed by the canonical normal form. -/
theorem fgcRatOfIntMul (leftValue rightValue : Int) :
    qnfMul (qnfOfInt leftValue) (qnfOfInt rightValue) = qnfOfInt (leftValue * rightValue) :=
  qnfNormalizeFixesCanonical (qnfOfInt (leftValue * rightValue))

/-- The canonical ℕ→ℚ embedding, `order/1`. -/
def fgcNatToRat (order : Nat) : QnfRat :=
  qnfOfInt (Int.ofNat order)

/-- The natural-number-to-rational multiplicative homomorphism
`fgcNatToRat (a*b) = fgcNatToRat a * fgcNatToRat b`, from the integer
homomorphism and `Int.ofNat` preserving multiplication. -/
theorem fgcNatToRatMul (leftOrder rightOrder : Nat) :
    qnfMul (fgcNatToRat leftOrder) (fgcNatToRat rightOrder) =
      fgcNatToRat (Nat.mul leftOrder rightOrder) := by
  show qnfMul (qnfOfInt (Int.ofNat leftOrder)) (qnfOfInt (Int.ofNat rightOrder)) =
    qnfOfInt (Int.ofNat (Nat.mul leftOrder rightOrder))
  rw [fgcRatOfIntMul (Int.ofNat leftOrder) (Int.ofNat rightOrder)]
  rfl

/-- A positive-order embedding is nonzero — its numerator is a successor. -/
theorem fgcNatToRatSuccNeZero (orderPredecessor : Nat) :
    fgcNatToRat (orderPredecessor + 1) ≠ qnfZero :=
  fun isEqual =>
    Int.noConfusion
      (congrArg (fun value => value.reducedPair.numerator) isEqual)
      (fun magnitudesEqual => Nat.noConfusion magnitudesEqual)

/-- `0 · order = 0` on ℕ — structural induction, both arms definitional. -/
theorem fgcNatMulZeroLeft : (order : Nat) → Nat.mul 0 order = 0
  | 0 => rfl
  | orderPredecessor + 1 => fgcNatMulZeroLeft orderPredecessor

/-! ## The carrier, the reciprocal, the cardinality -/

/-- A finite groupoid presented by its skeleton: one automorphism-group order
per isomorphism class.  Well-formedness is the separate predicate
`fgcIsWellFormed`. -/
structure FgcGroupoid where
  autOrders : List Nat

/-- The reciprocal `1/order` of one iso-class' automorphism order. -/
def fgcReciprocal (order : Nat) : QnfRat :=
  qnfInv (fgcNatToRat order)

/-- The reciprocal sum over a list of orders — a cons-only `qnfAdd` fold. -/
def fgcReciprocalSum : List Nat → QnfRat
  | [] => qnfZero
  | order :: rest => qnfAdd (fgcReciprocal order) (fgcReciprocalSum rest)

/-- Groupoid cardinality: `Σ 1/|Aut(x)|` over the iso-class skeleton. -/
def fgcCardinality (groupoid : FgcGroupoid) : QnfRat :=
  fgcReciprocalSum groupoid.autOrders

/-- One order is positive (≥ 1). -/
def fgcOrderIsPositive (order : Nat) : Bool :=
  Nat.ble 1 order

/-- Every order in a skeleton is positive. -/
def fgcAllOrdersPositive : List Nat → Bool
  | [] => true
  | order :: rest => fgcOrderIsPositive order && fgcAllOrdersPositive rest

/-- Well-formedness: every automorphism order is at least one. -/
def fgcIsWellFormed (groupoid : FgcGroupoid) : Bool :=
  fgcAllOrdersPositive groupoid.autOrders

/-- The empty groupoid — no iso-classes, cardinality `0`. -/
def fgcEmpty : FgcGroupoid :=
  { autOrders := [] }

/-- The point — one iso-class with trivial automorphism group, cardinality `1`. -/
def fgcPoint : FgcGroupoid :=
  { autOrders := [1] }

/-- One object with automorphism group `Z/2`, cardinality `1/2`. -/
def fgcTwoAut : FgcGroupoid :=
  { autOrders := [2] }

/-- One object with automorphism group `Z/3`, cardinality `1/3`. -/
def fgcThreeAut : FgcGroupoid :=
  { autOrders := [3] }

/-- Two rigid points, cardinality `2`. -/
def fgcTwoPoints : FgcGroupoid :=
  { autOrders := [1, 1] }

/-- Two objects each with automorphism group `Z/2`, cardinality
`1/2 + 1/2 = 1`. -/
def fgcTwoHalves : FgcGroupoid :=
  { autOrders := [2, 2] }

/-! ## Disjoint union is addition -/

/-- Cons-only concatenation of two skeletons, avoiding the propext-leaking
`List.append` lemmas. -/
def fgcListCat : List Nat → List Nat → List Nat
  | [], right => right
  | order :: rest, right => order :: fgcListCat rest right

/-- The disjoint union of two groupoids — concatenate the skeletons. -/
def fgcDisjointUnion (leftGroupoid rightGroupoid : FgcGroupoid) : FgcGroupoid :=
  { autOrders := fgcListCat leftGroupoid.autOrders rightGroupoid.autOrders }

/-- Append splits the reciprocal sum: the disjoint-union addition kernel. -/
theorem fgcReciprocalSumCat : (leftOrders rightOrders : List Nat) →
    fgcReciprocalSum (fgcListCat leftOrders rightOrders) =
      qnfAdd (fgcReciprocalSum leftOrders) (fgcReciprocalSum rightOrders)
  | [], rightOrders => (qnfAddZeroLeft (fgcReciprocalSum rightOrders)).symm
  | order :: leftRest, rightOrders => by
      show qnfAdd (fgcReciprocal order) (fgcReciprocalSum (fgcListCat leftRest rightOrders))
        = qnfAdd (qnfAdd (fgcReciprocal order) (fgcReciprocalSum leftRest))
            (fgcReciprocalSum rightOrders)
      rw [fgcReciprocalSumCat leftRest rightOrders,
        qnfAddAssoc (fgcReciprocal order) (fgcReciprocalSum leftRest)
          (fgcReciprocalSum rightOrders)]

/-- Disjoint union is addition: `card (G ⊔ H) = card G + card H`. -/
theorem fgcCardinalityUnion (leftGroupoid rightGroupoid : FgcGroupoid) :
    fgcCardinality (fgcDisjointUnion leftGroupoid rightGroupoid) =
      qnfAdd (fgcCardinality leftGroupoid) (fgcCardinality rightGroupoid) :=
  fgcReciprocalSumCat leftGroupoid.autOrders rightGroupoid.autOrders

/-- Union with the empty groupoid on the right is a cardinality identity. -/
theorem fgcCardinalityUnionEmptyRight (groupoid : FgcGroupoid) :
    fgcCardinality (fgcDisjointUnion groupoid fgcEmpty) = fgcCardinality groupoid := by
  rw [fgcCardinalityUnion]
  exact qnfAddZeroRight (fgcCardinality groupoid)

/-- Union with the empty groupoid on the left is a cardinality identity. -/
theorem fgcCardinalityUnionEmptyLeft (groupoid : FgcGroupoid) :
    fgcCardinality (fgcDisjointUnion fgcEmpty groupoid) = fgcCardinality groupoid := by
  rw [fgcCardinalityUnion]
  exact qnfAddZeroLeft (fgcCardinality groupoid)

/-! ## Product is multiplication

The product law rests on reciprocal multiplicativity `fgcReciprocalMul`,
`1/(a*b) = (1/a)*(1/b)`, applied across the product grid of automorphism
orders. -/

/-- Reciprocal multiplicativity `1/(a*b) = (1/a)*(1/b)`, unconditional on the
naturals: zero orders collapse both sides by multiplicative zero, positive
orders use inverse distributivity and the natural-number homomorphism. -/
theorem fgcReciprocalMul (leftOrder rightOrder : Nat) :
    fgcReciprocal (Nat.mul leftOrder rightOrder) =
      qnfMul (fgcReciprocal leftOrder) (fgcReciprocal rightOrder) := by
  cases rightOrder with
  | zero =>
      show fgcReciprocal 0 = qnfMul (fgcReciprocal leftOrder) (fgcReciprocal 0)
      exact (fgcMulZeroRight (fgcReciprocal leftOrder)).symm
  | succ rightPredecessor =>
      cases leftOrder with
      | zero =>
          rw [fgcNatMulZeroLeft (rightPredecessor + 1)]
          exact (fgcMulZeroLeft (fgcReciprocal (rightPredecessor + 1))).symm
      | succ leftPredecessor =>
          show qnfInv (fgcNatToRat (Nat.mul (leftPredecessor + 1) (rightPredecessor + 1)))
            = qnfMul (qnfInv (fgcNatToRat (leftPredecessor + 1)))
                (qnfInv (fgcNatToRat (rightPredecessor + 1)))
          rw [← fgcNatToRatMul (leftPredecessor + 1) (rightPredecessor + 1),
            fgcInvMulDistrib (fgcNatToRatSuccNeZero leftPredecessor)
              (fgcNatToRatSuccNeZero rightPredecessor)]

/-- One row of the product grid: fix a left order and multiply it against every
right order (the automorphism group of a product object is the product). -/
def fgcProductRow (leftOrder : Nat) : List Nat → List Nat
  | [] => []
  | rightOrder :: rest => Nat.mul leftOrder rightOrder :: fgcProductRow leftOrder rest

/-- The full product skeleton: every left order crossed with every right order. -/
def fgcProductOrders : List Nat → List Nat → List Nat
  | [], _rightOrders => []
  | leftOrder :: leftRest, rightOrders =>
      fgcListCat (fgcProductRow leftOrder rightOrders) (fgcProductOrders leftRest rightOrders)

/-- The product of two groupoids — the product skeleton. -/
def fgcProduct (leftGroupoid rightGroupoid : FgcGroupoid) : FgcGroupoid :=
  { autOrders := fgcProductOrders leftGroupoid.autOrders rightGroupoid.autOrders }

/-- A product row's reciprocal sum is `(1/leftOrder) * (right-hand sum)`, from
reciprocal multiplicativity and left distributivity. -/
theorem fgcProductRowSum (leftOrder : Nat) : (rightOrders : List Nat) →
    fgcReciprocalSum (fgcProductRow leftOrder rightOrders) =
      qnfMul (fgcReciprocal leftOrder) (fgcReciprocalSum rightOrders)
  | [] => (fgcMulZeroRight (fgcReciprocal leftOrder)).symm
  | rightOrder :: rest => by
      show qnfAdd (fgcReciprocal (Nat.mul leftOrder rightOrder))
          (fgcReciprocalSum (fgcProductRow leftOrder rest))
        = qnfMul (fgcReciprocal leftOrder)
            (qnfAdd (fgcReciprocal rightOrder) (fgcReciprocalSum rest))
      rw [fgcReciprocalMul leftOrder rightOrder, fgcProductRowSum leftOrder rest,
        qnfMulLeftDistrib (fgcReciprocal leftOrder) (fgcReciprocal rightOrder)
          (fgcReciprocalSum rest)]

/-- The product skeleton's reciprocal sum is the product of the two sums: the
product-is-multiplication kernel. -/
theorem fgcProductOrdersSum : (leftOrders rightOrders : List Nat) →
    fgcReciprocalSum (fgcProductOrders leftOrders rightOrders) =
      qnfMul (fgcReciprocalSum leftOrders) (fgcReciprocalSum rightOrders)
  | [], rightOrders => (fgcMulZeroLeft (fgcReciprocalSum rightOrders)).symm
  | leftOrder :: leftRest, rightOrders => by
      show fgcReciprocalSum
          (fgcListCat (fgcProductRow leftOrder rightOrders)
            (fgcProductOrders leftRest rightOrders))
        = qnfMul (qnfAdd (fgcReciprocal leftOrder) (fgcReciprocalSum leftRest))
            (fgcReciprocalSum rightOrders)
      rw [fgcReciprocalSumCat (fgcProductRow leftOrder rightOrders)
          (fgcProductOrders leftRest rightOrders),
        fgcProductRowSum leftOrder rightOrders,
        fgcProductOrdersSum leftRest rightOrders,
        qnfMulRightDistrib (fgcReciprocal leftOrder) (fgcReciprocalSum leftRest)
          (fgcReciprocalSum rightOrders)]

/-- Product is multiplication: `card (G × H) = card G · card H`. -/
theorem fgcCardinalityProduct (leftGroupoid rightGroupoid : FgcGroupoid) :
    fgcCardinality (fgcProduct leftGroupoid rightGroupoid) =
      qnfMul (fgcCardinality leftGroupoid) (fgcCardinality rightGroupoid) :=
  fgcProductOrdersSum leftGroupoid.autOrders rightGroupoid.autOrders

/-- The point has cardinality one — `1/1 + 0`, collapsed by `qnfAddZeroRight`. -/
theorem fgcCardinalityPoint : fgcCardinality fgcPoint = qnfOne := by
  show qnfAdd qnfOne qnfZero = qnfOne
  exact qnfAddZeroRight qnfOne

/-- Product with the point on the right is a cardinality identity. -/
theorem fgcCardinalityProductPointRight (groupoid : FgcGroupoid) :
    fgcCardinality (fgcProduct groupoid fgcPoint) = fgcCardinality groupoid := by
  rw [fgcCardinalityProduct, fgcCardinalityPoint, qnfMulOneRight]

/-- Product with the point on the left is a cardinality identity. -/
theorem fgcCardinalityProductPointLeft (groupoid : FgcGroupoid) :
    fgcCardinality (fgcProduct fgcPoint groupoid) = fgcCardinality groupoid := by
  rw [fgcCardinalityProduct, fgcCardinalityPoint, qnfMulOneLeft]

/-! ## Non-injectivity and out-of-scope extensions -/

/-- Non-injectivity of decategorification: the point `[1]` and the two-object
groupoid `[2,2]` (each object with automorphism group of order two) are not
equivalent yet share cardinality `1`.  Both reciprocal sums reduce to the
canonical `1/1`, so the equality holds by `rfl` and no rational determines a
unique groupoid. -/
theorem fgcInverseAmbiguityWitness :
    fgcCardinality fgcPoint = fgcCardinality fgcTwoHalves := rfl

/-- The three extensions beyond the finite skeleton model that are out of scope:
inverse categorification, infinite-groupoid cardinality, and equivalence of
groupoids from raw generators and relations, all detailed in the module
header. -/
def fgcHasGroupoidExtensions : Bool := false

/-! ## Capability summary -/

/-- Finite-groupoid cardinality is a computable exact rational
(`fgcCardinality`), the reciprocal sum over the iso-class skeleton, and its two
decategorification laws hold as zero-axiom theorems: disjoint union is addition
(`fgcCardinalityUnion`) and product is multiplication (`fgcCardinalityProduct`),
with the empty- and point-unit laws and the reciprocal-multiplicativity lemma
`fgcReciprocalMul`. -/
def fgcHasGroupoidCardinality : Bool := true

/-! ## Worked examples -/

/-- The empty groupoid has cardinality zero. -/
theorem fgcFireEmptyCardinality : fgcCardinality fgcEmpty = qnfZero := rfl

/-- A single object with automorphism group of order two has cardinality `1/2`. -/
theorem fgcFireTwoAutCardinality :
    fgcCardinality fgcTwoAut = qnfNormalize { numerator := 1, denominatorPredecessor := 1 } := rfl

/-- Two rigid points have cardinality `2`. -/
theorem fgcFireTwoPointsCardinality :
    fgcCardinality fgcTwoPoints = qnfNormalize { numerator := 2, denominatorPredecessor := 0 } := rfl

/-- Disjoint union is addition on a concrete pair of order-two-automorphism
objects. -/
theorem fgcFireUnionAddition :
    fgcCardinality (fgcDisjointUnion fgcTwoAut fgcTwoAut) =
      qnfAdd (fgcCardinality fgcTwoAut) (fgcCardinality fgcTwoAut) :=
  fgcCardinalityUnion fgcTwoAut fgcTwoAut

/-- The product of `[2]` and `[3]` is the skeleton `[6]`. -/
theorem fgcFireProductOrdersSixth :
    (fgcProduct fgcTwoAut fgcThreeAut).autOrders = [6] := rfl

/-- Product is multiplication computed: `card [2] * card [3] = 1/6`. -/
theorem fgcFireProductSixthValue :
    fgcCardinality (fgcProduct fgcTwoAut fgcThreeAut) =
      qnfNormalize { numerator := 1, denominatorPredecessor := 5 } := rfl

end FX1Poly.ComputerAlgebra
