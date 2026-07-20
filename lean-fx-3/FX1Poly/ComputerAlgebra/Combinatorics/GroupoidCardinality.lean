import FX1Poly.ComputerAlgebra.Number.NormalizedRational

/-! # ComputerAlgebra/Combinatorics/GroupoidCardinality — finite-groupoid
cardinality as decategorification (CSHD)

The groupoid cardinality of Baez-Dolan: a finite groupoid presented by its
skeleton — one automorphism-group order per isomorphism class — has a
cardinality `Σ 1/|Aut(x)|`, an exact rational.  This is the decategorified
shadow of a category: a NUMBER read off a groupoid, with the two structural
laws that make it a `Rig` homomorphism —

  * **disjoint union is addition**: `card (G ⊔ H) = card G + card H`;
  * **product is multiplication**: `card (G × H) = card G · card H`,

the second riding the reciprocal-multiplicativity fact `1/(a·b) = (1/a)·(1/b)`
(the automorphism group of a product object is the product of the automorphism
groups).

Built directly on the canonical-NF ℚ carrier `QnfRat` (NUM-Q-7): a finite
`List Nat` of automorphism-group orders, cardinality a cons-only `qnfAdd`
fold of reciprocals `qnfInv (qnfOfInt (Int.ofNat order))`.  The addition law
is the append-splits-sum shape shared with the shipped `fpdMassSumCat`; the
product law adds one genuinely new arithmetic brick — reciprocal
multiplicativity — proved by field-law inverse-uniqueness plus the ℕ→ℚ
multiplicative homomorphism (both from the shipped `QnfRat` suite, no descent
to the setoid layer).

## What lands (DECIDED)

  * `FgcGroupoid` — the carrier (`autOrders : List Nat`), with
    `fgcIsWellFormed` (every order ≥ 1).
  * `fgcCardinality` — the reciprocal sum, with the four distinguished values
    (empty ↦ `0`, point ↦ `1`, one `Z/2` object ↦ `1/2`, two points ↦ `2`).
  * `fgcCardinalityUnion` — disjoint union is addition (structural, riding the
    append-splits-sum `fgcReciprocalSumCat`), plus both empty-unit laws.
  * `fgcCardinalityProduct` — product is multiplication (structural, riding the
    reciprocal-multiplicativity `fgcReciprocalMul` + the ℕ→ℚ homomorphism
    `fgcNatToRatMul` + inverse distributivity `fgcInvMulDistrib`), plus both
    point-unit laws.
  * `fgcInverseAmbiguityWitness` — the point and the two-`Z/2`-object groupoid
    share cardinality `1`: the concrete non-injectivity of decategorification.

## The walls (WALLED, `false` markers)

  * `fgcHasInverseCategorification := false` — recovering a groupoid from its
    rational cardinality is NOT a function (`fgcInverseAmbiguityWitness` is the
    computable refutation: two non-equivalent groupoids at cardinality `1`).
  * `fgcHasInfiniteGroupoidCardinality := false` — an infinite groupoid's
    cardinality is a convergent real series (the groupoid of finite sets has
    cardinality `Σ 1/n! = e`); the finite `qnfAdd` fold has no completion.
    Same walled node as the MEAS-1 `fpdHasCountableSupport := false` (the
    Bishop-real L1 limit).
  * `fgcHasGroupoidEquivalenceDecision := false` — for the skeleton-list
    representation equivalence IS decidable (sort the orders, compare); the
    wall is deciding equivalence of two groupoids given by raw
    generators/relations (graph-isomorphism-hard + the group-order/orbit
    problem), the structural sibling of `cswHasPresentedCommWordDecision`.

## Zero-axiom

Structural recursion on `List` / `Nat` (never `WellFounded.fix`), full-enum
constructor matches (no wildcard arms over a split scrutinee), `QnfRat` kernel
arithmetic + its field-law suite, `congrArg`/`Eq.trans` and `calc` chains.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`, `funext`, `decide`-on-`Prop`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/Combinatorics/GroupoidCardinality.lean`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## Scalar `QnfRat` lemmas the product law needs

`qnfMulZeroRight`/`Left` live in the MEAS-1 probability file; re-derived here
(self-contained, no cross-import) alongside the multiplicative middle-four,
inverse uniqueness, product-nonzero, and inverse distributivity — all from the
shipped `QnfRat` field-law suite. -/

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

/-- The multiplicative middle-four exchange — `(a·b)·(c·d) = (a·c)·(b·d)` —
from commutativity and associativity. -/
theorem fgcMulMiddleFour (firstFactor secondFactor thirdFactor fourthFactor : QnfRat) :
    qnfMul (qnfMul firstFactor secondFactor) (qnfMul thirdFactor fourthFactor) =
      qnfMul (qnfMul firstFactor thirdFactor) (qnfMul secondFactor fourthFactor) := by
  rw [qnfMulAssoc firstFactor secondFactor (qnfMul thirdFactor fourthFactor),
    ← qnfMulAssoc secondFactor thirdFactor fourthFactor,
    qnfMulComm secondFactor thirdFactor,
    qnfMulAssoc thirdFactor secondFactor fourthFactor,
    ← qnfMulAssoc firstFactor thirdFactor (qnfMul secondFactor fourthFactor)]

/-- **Inverse uniqueness**: a right multiplicative inverse of a nonzero value IS
the canonical inverse — multiply through by `qnfInv base` and collapse. -/
theorem fgcInverseUnique {base other : QnfRat} (baseNonzero : base ≠ qnfZero)
    (isInverse : qnfMul base other = qnfOne) : other = qnfInv base := by
  calc other = qnfMul qnfOne other := (qnfMulOneLeft other).symm
    _ = qnfMul (qnfMul (qnfInv base) base) other := by rw [qnfInvMulCancels baseNonzero]
    _ = qnfMul (qnfInv base) (qnfMul base other) := qnfMulAssoc _ _ _
    _ = qnfMul (qnfInv base) qnfOne := by rw [isInverse]
    _ = qnfInv base := qnfMulOneRight _

/-- A product of nonzero values is nonzero — cancel the left factor by its
inverse against a hypothetical zero product. -/
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

/-- **Inverse distributes over multiplication** on nonzero factors:
`(x·y)⁻¹ = x⁻¹·y⁻¹`.  The candidate `x⁻¹·y⁻¹` is a right inverse of `x·y` by the
middle-four exchange, then inverse uniqueness pins it. -/
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

/-- The ℤ→ℚ multiplicative homomorphism: `(a/1)·(b/1) = (a·b)/1` — the canonical
integer embeddings' product is the embedding of the product, since
`mulExact` of two `value/1` pairs is definitionally `(value·value)/1`, fixed by
the canonical normal form. -/
theorem fgcRatOfIntMul (leftValue rightValue : Int) :
    qnfMul (qnfOfInt leftValue) (qnfOfInt rightValue) = qnfOfInt (leftValue * rightValue) :=
  qnfNormalizeFixesCanonical (qnfOfInt (leftValue * rightValue))

/-- The canonical ℕ→ℚ embedding, `order/1`. -/
def fgcNatToRat (order : Nat) : QnfRat :=
  qnfOfInt (Int.ofNat order)

/-- The ℕ→ℚ multiplicative homomorphism: `fgcNatToRat (a·b) =
fgcNatToRat a · fgcNatToRat b` — the ℤ homomorphism plus `Int.ofNat` being a
multiplicative homomorphism definitionally. -/
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

/-! ## T1 — the carrier, the reciprocal, the cardinality -/

/-- A finite groupoid presented by its skeleton: one automorphism-group order
per isomorphism class.  Well-formedness (every order ≥ 1) is a separate
predicate `fgcIsWellFormed`, not baked into the carrier. -/
structure FgcGroupoid where
  autOrders : List Nat

/-- The reciprocal `1/order` of one iso-class' automorphism order. -/
def fgcReciprocal (order : Nat) : QnfRat :=
  qnfInv (fgcNatToRat order)

/-- The reciprocal sum over a list of orders — a cons-only `qnfAdd` fold. -/
def fgcReciprocalSum : List Nat → QnfRat
  | [] => qnfZero
  | order :: rest => qnfAdd (fgcReciprocal order) (fgcReciprocalSum rest)

/-- **Groupoid cardinality**: `Σ 1/|Aut(x)|` over the iso-class skeleton. -/
def fgcCardinality (groupoid : FgcGroupoid) : QnfRat :=
  fgcReciprocalSum groupoid.autOrders

/-- One order is positive (≥ 1). -/
def fgcOrderIsPositive (order : Nat) : Bool :=
  Nat.ble 1 order

/-- Every order in a skeleton is positive. -/
def fgcAllOrdersPositive : List Nat → Bool
  | [] => true
  | order :: rest => fgcOrderIsPositive order && fgcAllOrdersPositive rest

/-- **Well-formedness**: every automorphism order is at least one (a group has
at least its identity). -/
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

/-- Two objects each with automorphism group `Z/2`, cardinality `1/2 + 1/2 = 1`
— the decategorification-ambiguity partner of the point. -/
def fgcTwoHalves : FgcGroupoid :=
  { autOrders := [2, 2] }

/-! ## T2 — disjoint union is addition -/

/-- Cons-only concatenation of two skeletons (own list op — avoids the
propext-leak-prone `List.append` lemmas). -/
def fgcListCat : List Nat → List Nat → List Nat
  | [], right => right
  | order :: rest, right => order :: fgcListCat rest right

/-- The disjoint union of two groupoids — concatenate the skeletons. -/
def fgcDisjointUnion (leftGroupoid rightGroupoid : FgcGroupoid) : FgcGroupoid :=
  { autOrders := fgcListCat leftGroupoid.autOrders rightGroupoid.autOrders }

/-- **Append splits the reciprocal sum** — the decategorification addition
kernel (same shape as the shipped `fpdMassSumCat`). -/
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

/-- **DISJOINT UNION IS ADDITION**: `card (G ⊔ H) = card G + card H`. -/
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

/-! ## T3 — product is multiplication

The reciprocal-multiplicativity brick `fgcReciprocalMul` (`1/(a·b) =
(1/a)·(1/b)`) makes the product law port the `fpdProductSupportMassSum` shape
verbatim with the reciprocal in the mass column. -/

/-- **Reciprocal multiplicativity**: `1/(a·b) = (1/a)·(1/b)`, unconditional on
ℕ — zero orders collapse both sides (`fgcMulZeroRight`/`Left`), positive orders
ride the inverse-distributivity + ℕ→ℚ-homomorphism bricks. -/
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

/-- A product row's reciprocal sum is `(1/leftOrder) · (right's sum)` — riding
reciprocal multiplicativity + left distributivity. -/
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

/-- The product skeleton's reciprocal sum is the product of the sums — the
decategorification multiplication kernel (same shape as
`fpdProductSupportMassSum`). -/
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

/-- **PRODUCT IS MULTIPLICATION**: `card (G × H) = card G · card H`. -/
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

/-! ## T4 — the walls -/

/-- WALLED: decategorification has no computable inverse — recovering a groupoid
from its rational cardinality is NOT a function.  Concrete obstruction:
`fgcInverseAmbiguityWitness` — the point `[1]` (cardinality `1`) and the
two-`Z/2`-object groupoid `[2,2]` (cardinality `1/2 + 1/2 = 1`) are
non-equivalent groupoids sharing cardinality `1`, so no rational determines a
unique groupoid.

Burned attack A: "invert by reading the reciprocal-sum backwards" — the sum
`1` decomposes as `1/1`, as `1/2 + 1/2`, as `1/3 + 1/3 + 1/3`, …; the
decomposition is a partition-of-a-rational problem with infinitely many
solutions, not a function.  Burned attack B: "restrict to a canonical
decomposition (e.g. all-singletons)" — that only recovers the DISCRETE groupoid
with `card` copies of the point; every groupoid with nontrivial automorphisms
(any order ≥ 2) is then unrecoverable, so the map is not a section. -/
def fgcHasInverseCategorification : Bool := false

/-- WALLED: the cardinality of an infinite groupoid is a convergent real series,
out of finite-`QnfRat` scope.  The groupoid of finite sets has cardinality
`Σ_{n≥0} 1/n! = e`, an irrational limit; the finite `qnfAdd` fold represents no
infinite tail.  Same walled node as the MEAS-1 `fpdHasCountableSupport := false`
(the missing Bishop-real L1 completion).

Burned attack A: "extend the fold to a lazy stream and take the limit" — `QnfRat`
has no completion in this layer; the limit lives in `RegularReal`, and no finite
`List Nat` presents `1/n!` for all `n`.  Burned attack B: "bound by a rational
tail estimate and pin an interval" — that gives a `RegularReal` Cauchy witness,
not a `QnfRat`; the deliverable's cardinality type is exact-rational, so the
infinite case is a genuinely different (real-valued) construction. -/
def fgcHasInfiniteGroupoidCardinality : Bool := false

/-- WALLED: deciding groupoid equivalence from a RAW presentation
(generators/relations) is out of scope — it is graph-isomorphism-hard, and
extracting the automorphism-order skeleton is the group-order/orbit problem.
For the SKELETON-list representation used here equivalence IS decidable (sort
the orders with `cswSort`, compare with `cswListNatBeq`); the wall is only the
presented case, the structural sibling of `cswHasPresentedCommWordDecision`
(deciding a congruence from a presentation, not from a normal form).

Burned attack A: "compare skeletons directly" — decides the skeleton case, not
the presented case (which first requires computing the skeleton).  Burned
attack B: "enumerate isomorphisms of the presentation graphs" — that IS the
graph-isomorphism search this wall names; no zero-axiom polynomial procedure is
in scope. -/
def fgcHasGroupoidEquivalenceDecision : Bool := false

/-- The computable non-injectivity witness: the point and the two-`Z/2`-object
groupoid — non-equivalent — share cardinality `1`.  Both reciprocal sums reduce
to the canonical `1/1`, so the equality is a kernel `rfl`; decategorification
therefore cannot be inverted. -/
theorem fgcInverseAmbiguityWitness :
    fgcCardinality fgcPoint = fgcCardinality fgcTwoHalves := rfl

/-! ## Content markers -/

/-- DECIDED: finite-groupoid cardinality is a computable exact rational
(`fgcCardinality`), the reciprocal sum over the iso-class skeleton. -/
def fgcHasGroupoidCardinality : Bool := true

/-- DECIDED: the two decategorification laws hold as zero-axiom structural
theorems — disjoint union is addition (`fgcCardinalityUnion`) and product is
multiplication (`fgcCardinalityProduct`), with the empty- and point-unit laws
and the reciprocal-multiplicativity brick `fgcReciprocalMul`. -/
def fgcHasDecategorificationLaws : Bool := true

/-! ## Fires -/

/-- Fire: the empty groupoid has cardinality zero. -/
theorem fgcFireEmptyCardinality : fgcCardinality fgcEmpty = qnfZero := rfl

/-- Fire: the one-`Z/2` groupoid has cardinality `1/2`. -/
theorem fgcFireTwoAutCardinality :
    fgcCardinality fgcTwoAut = qnfNormalize { numerator := 1, denominatorPredecessor := 1 } := rfl

/-- Fire: the two-rigid-points groupoid has cardinality `2`. -/
theorem fgcFireTwoPointsCardinality :
    fgcCardinality fgcTwoPoints = qnfNormalize { numerator := 2, denominatorPredecessor := 0 } := rfl

/-- Fire: disjoint union is addition on a concrete pair (two `Z/2` objects). -/
theorem fgcFireUnionAddition :
    fgcCardinality (fgcDisjointUnion fgcTwoAut fgcTwoAut) =
      qnfAdd (fgcCardinality fgcTwoAut) (fgcCardinality fgcTwoAut) :=
  fgcCardinalityUnion fgcTwoAut fgcTwoAut

/-- Fire: the product of `[2]` and `[3]` is the skeleton `[6]`. -/
theorem fgcFireProductOrdersSixth :
    (fgcProduct fgcTwoAut fgcThreeAut).autOrders = [6] := rfl

/-- Fire: `card [2] × card [3] = 1/6` — product is multiplication, computed. -/
theorem fgcFireProductSixthValue :
    fgcCardinality (fgcProduct fgcTwoAut fgcThreeAut) =
      qnfNormalize { numerator := 1, denominatorPredecessor := 5 } := rfl

end FX1Poly.ComputerAlgebra
