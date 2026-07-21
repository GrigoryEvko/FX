import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisorThree

/-! # IntPolynomialDeterminantalDivisorGeneral — the uniform general-n determinantal-divisor engine

The dimension-2 and 3 determinantal divisors hand-list the index selections; the engine underneath is
already general (`polyGcdList` folds the ℤ[x] GCD over any list of minors, `charMatrixMinor k` yields the
`k×k` polynomial minor for any selection functions), so the one missing primitive is a general `k`-subset
index enumerator.  This file supplies it, closing the scale-up.  It is the parent of the determinantal /
invariant-factor / char-matrix sub-arc, whose markers are consolidated here (see
`fxIntPoly_hasGeneralDeterminantalDivisorEngine`).

  * `indicesBelow n = [0, 1, …, n−1]` as data (cons/append, not `List.range` whose lemmas leak `propext`).
  * `kSublists k available` = the order-preserving `k`-element sublists of `available`, by the take/skip
    recursion `(map (first :: ·) (kSublists k rest)) ++ kSublists (k+1) rest`.
  * `kSubsets k n = kSublists k (indicesBelow n)` = all `k`-subsets of `{0, …, n−1}`.
  * `selectionOf chosen` = the `Nat → Nat` selector reading position `i` to the `i`-th chosen index — the
    structural, `propext`-free replacement for `List.getD`, feeding `charMatrixMinor` unchanged.

`charDeterminantalDivisor k n M` is the ℤ[x] GCD of the `k×k` minors of `x·I − M` over all pairs of
`k`-subsets — the `k`-th determinantal divisor `d_k` at arbitrary `n`; its degree list
`determinantalDivisorSignature n M = [deg d₁, …, deg d_n]` is a decidable similarity invariant.  The engine
is cross-validated by `decide`-agreement with the hand-rolled dimension-2 and 3 divisors, and reaches the
full dim-3 signatures `[0,0,3]/[0,1,3]/[1,2,3]` that separate all three classes of char poly `(x−2)³`.

Structural enumerator recursions + the shipped GCD/minor machinery + `decide` groundings.  Free of `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The k-subset index enumerator -/

/-- `[0, 1, …, n−1]` built as data (cons/append), avoiding `List.range` whose characterization lemmas
leak `propext`. -/
def indicesBelow : Nat → List Nat
  | 0 => []
  | index + 1 => indicesBelow index ++ [index]

/-- The order-preserving `k`-element sublists of `available`.  The `k+1, first :: rest` arm splits into
"take `first`" (`map (first :: ·)` over the `k`-sublists of `rest`) appended with "skip `first`" (the
`(k+1)`-sublists of `rest`).  Fully-enumerated arms `(0, _)`, `(_+1, [])`, `(_+1, _ :: _)` with a constant
`List (List Nat)` motive keep it `propext`-free. -/
def kSublists : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | count + 1, first :: rest =>
      (kSublists count rest).map (fun chosen => first :: chosen) ++ kSublists (count + 1) rest

/-- All `k`-subsets of `{0, …, n−1}`, order-preserving. -/
def kSubsets (subsetSize dimension : Nat) : List (List Nat) :=
  kSublists subsetSize (indicesBelow dimension)

/-- The `Nat → Nat` selector reading position `i` to the `i`-th chosen index — the structural,
`propext`-free replacement for `List.getD` (out-of-range positions map to `0`).  Feeds the shipped
`charMatrixMinor` unchanged. -/
def selectionOf : List Nat → Nat → Nat
  | [], _ => 0
  | value :: _, 0 => value
  | _ :: rest, position + 1 => selectionOf rest position

/-! ## The general determinantal divisor -/

/-- All `k×k` minors of the characteristic matrix `x·I − M` over every pair of `k`-subsets of
`{0, …, n−1}` — the raw list whose ℤ[x] GCD is the `k`-th determinantal divisor. -/
def allCharMinorsOfSize (subsetSize dimension : Nat) (matrix : SetoidMatrix Int) : List (List Int) :=
  (kSubsets subsetSize dimension).flatMap (fun rowSubset =>
    (kSubsets subsetSize dimension).map (fun colSubset =>
      charMatrixMinor subsetSize matrix (selectionOf rowSubset) (selectionOf colSubset)))

/-- The `k`-th determinantal divisor `d_k` of an `n×n` matrix at ARBITRARY `n`: the ℤ[x] GCD of all `k×k`
minors of `x·I − M`.  Fuel `64` is ample for the small dimensions grounded here. -/
def charDeterminantalDivisor (subsetSize dimension : Nat) (matrix : SetoidMatrix Int) : List Int :=
  polyGcdList 64 (allCharMinorsOfSize subsetSize dimension matrix)

/-- The full determinantal-divisor degree signature `[deg d₁, …, deg d_n]` of an `n×n` matrix — a
decidable similarity invariant computed uniformly at any dimension. -/
def determinantalDivisorSignature (dimension : Nat) (matrix : SetoidMatrix Int) : List Nat :=
  (indicesBelow dimension).map (fun index =>
    polyDegree (charDeterminantalDivisor (index + 1) dimension matrix))

/-! ## Enumerator groundings -/

/-- `{0,…,n−1}` as data: `indicesBelow 4 = [0,1,2,3]`. -/
theorem indicesBelowFourIsRange : indicesBelow 4 = [0, 1, 2, 3] := by decide

/-- The two `1`-subsets of `{0,1}`. -/
theorem kSubsetsOneTwoIsSingletons : kSubsets 1 2 = [[0], [1]] := by decide

/-- The three `2`-subsets of `{0,1,2}`. -/
theorem kSubsetsTwoThreeIsPairs : kSubsets 2 3 = [[0, 1], [0, 2], [1, 2]] := by decide

/-- All six `2`-subsets of `{0,1,2,3}` — a dimension the hand-rolled r34/r36 selectors never enumerated. -/
theorem kSubsetsTwoFourIsSixPairs :
    kSubsets 2 4 = [[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]] := by decide

/-! ## Cross-validation: the general engine reproduces the hand-rolled divisors -/

/-- At `n=2, k=1` the general engine reproduces `charMatrixDivisorOne` on every dim-2 archetype (scalar
`2·I`, Jordan `[[2,1],[0,2]]`, `diag(2,3)`) — byte-for-byte after trimming. -/
theorem generalDivisorAgreesWithHandRolledTwo :
    polyTrim (charDeterminantalDivisor 1 2 (twoByTwoMatrix 2 0 0 2))
        = polyTrim (charMatrixDivisorOne (twoByTwoMatrix 2 0 0 2))
    ∧ polyTrim (charDeterminantalDivisor 1 2 (twoByTwoMatrix 2 1 0 2))
        = polyTrim (charMatrixDivisorOne (twoByTwoMatrix 2 1 0 2))
    ∧ polyTrim (charDeterminantalDivisor 1 2 (twoByTwoMatrix 2 0 0 3))
        = polyTrim (charMatrixDivisorOne (twoByTwoMatrix 2 0 0 3)) := by decide

/-- At `n=3` the general engine reproduces `charMatrixDivisorOneAtThree` (k=1) and
`charMatrixDivisorTwoAtThree` (k=2) on all three `(x−2)³` archetypes. -/
theorem generalDivisorAgreesWithHandRolledThree :
    polyTrim (charDeterminantalDivisor 1 3 jordanBlockThree)
        = polyTrim (charMatrixDivisorOneAtThree jordanBlockThree)
    ∧ polyTrim (charDeterminantalDivisor 2 3 jordanBlockThree)
        = polyTrim (charMatrixDivisorTwoAtThree jordanBlockThree)
    ∧ polyTrim (charDeterminantalDivisor 1 3 jordanTwoPlusOne)
        = polyTrim (charMatrixDivisorOneAtThree jordanTwoPlusOne)
    ∧ polyTrim (charDeterminantalDivisor 2 3 jordanTwoPlusOne)
        = polyTrim (charMatrixDivisorTwoAtThree jordanTwoPlusOne)
    ∧ polyTrim (charDeterminantalDivisor 1 3 scalarThree)
        = polyTrim (charMatrixDivisorOneAtThree scalarThree)
    ∧ polyTrim (charDeterminantalDivisor 2 3 scalarThree)
        = polyTrim (charMatrixDivisorTwoAtThree scalarThree) := by decide

/-! ## New reach: the full dim-3 signatures, separating all three (x−2)³ classes uniformly -/

/-- The full dim-3 determinantal-divisor degree signature: `J₃(2) ↦ [0,0,3]`, `J₂⊕J₁ ↦ [0,1,3]`, `2·I₃ ↦
[1,2,3]` — pairwise distinct, so the general engine separates all three similarity classes of characteristic
polynomial `(x−2)³` in one uniform computation (`deg d₃ = 3 = deg(x−2)³` for all, as it must). -/
theorem fullSignatureSeparatesCubicClasses :
    determinantalDivisorSignature 3 jordanBlockThree = [0, 0, 3]
    ∧ determinantalDivisorSignature 3 jordanTwoPlusOne = [0, 1, 3]
    ∧ determinantalDivisorSignature 3 scalarThree = [1, 2, 3] := by decide

/-- Two matrices are declared dissimilar when their full determinantal-divisor degree signatures differ.
Reducible so a concrete separation closes by `decide`. -/
@[reducible] def DissimilarBySignature (source target : SetoidMatrix Int) (dimension : Nat) : Prop :=
  determinantalDivisorSignature dimension source ≠ determinantalDivisorSignature dimension target

/-- The three `(x−2)³` classes are pairwise non-similar, decided by the uniform general-engine signature. -/
theorem generalEngineSeparatesAllThreeCubicClasses :
    DissimilarBySignature jordanBlockThree jordanTwoPlusOne 3
    ∧ DissimilarBySignature jordanBlockThree scalarThree 3
    ∧ DissimilarBySignature jordanTwoPlusOne scalarThree 3 := by decide

/-! ## The marker -/

/-- Consolidated marker for the ℤ[x] determinantal-divisor / invariant-factor / char-matrix sub-arc.
Covers: the `k`-subset enumerator and the uniform general-`n` determinantal-divisor engine
(`charDeterminantalDivisor k n`, `determinantalDivisorSignature n`) cross-validated against the hand-rolled
divisors and reaching the full dim-3 signatures `[0,0,3]/[0,1,3]/[1,2,3]` (this file); the k×k characteristic
minors over ℤ[x] (`IntPolynomialCharMinors`); the first determinantal divisor and its dimension-2 similarity
separator (`IntPolynomialDeterminantalDivisor`); the dimension-3 three-way separation of char poly `(x−2)³`
(`IntPolynomialDeterminantalDivisorThree`); the invariant factors and rational-canonical-form block count at
dimension 2 (`IntPolynomialInvariantFactors`); and the completeness of the subset enumerator
(`IntPolynomialSubsetEnumeratorComplete`). -/
def fxIntPoly_hasGeneralDeterminantalDivisorEngine : Bool := true

end FX1Poly.ComputerAlgebra
