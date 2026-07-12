import FX1Poly.Polygraph.Homology.PeriodicTowerCohomologyCupProduct
import FX1Poly.ComputerAlgebra.Number.IntNegation

/-! # FX1Poly/Polygraph/Homology/PeriodicTowerDiagonalChainMap — the explicit Cartan-Eilenberg /
    Roberts diagonal `Delta : W -> W (X) W` on the `ZZ/n` periodic resolution, MACHINE-CHECKED as a
    chain map, and the cup product it induces re-derived from the diagonal (TOWER-RING, #2147, r2)

The r1 opener `PeriodicTowerCohomologyCupProduct` shipped the cup product on the even subring `ZZ[x]`
as DATA on canonical representatives, with the even-degree diagonal SHUFFLE `Sum_{i+j=k} e_{2i} (X)
e_{2j}` (`diagonalEvenShuffle`) — the even-even component of the full diagonal — and named the verified
`G`-chain-map diagonal `Delta : W -> W (X) W` as the honest r2 residual.  This module supplies that
diagonal: the full four-parity-component formula (Roberts, *The Cohomology Ring of a Finite Abelian
Group*, Thm 4.3.3; Cartan-Eilenberg Ch. XII), its verification as a chain map (`Delta . boundary =
tensorBoundary . Delta`) at `n = 2, 3, 5` for degrees 1..5, and the derived-cup agreement theorem
re-founding the r1 products on the diagonal.

## The formulas (period 2; probe-pinned before any proof, `#eval` on n = 2, 3, 5 deg 1..5)

The resolution `W` over `ZZ[G]`, `G = ZZ/n = <t | t^n = 1>`, has one generator `e_p` per degree `p`
(`e_{2i} = sigma^(i)`, `e_{2i+1} = tau sigma^(i)` in Roberts' divided-power notation), with

  `boundary e_{2i+1} = (t - 1) e_{2i}`,   `boundary e_{2i} = N e_{2i-1}` (`i > 0`),   `boundary e_0 = 0`,

`N = 1 + t + ... + t^(n-1)`.  The diagonal (Roberts Thm 4.3.3, translated to `e_p / t` notation):

  `Delta e_0       = e_0 (X) e_0`
  `Delta e_{2k+1}  = Sum_{i+j=k} [ e_{2i+1} (X) (t . e_{2j})  +  e_{2i} (X) e_{2j+1} ]`
  `Delta e_{2k}    = Sum_{i+j=k}   e_{2i} (X) e_{2j}
                   + Sum_{i+j=k-1} Sum_{0<=a<b<n}  t^a e_{2i+1} (X) t^b e_{2j+1}`

with the Koszul tensor differential `boundaryTensor (x (X) y) = (boundary x) (X) y + (-1)^{deg x} x (X)
(boundary y)`.  The `t`-twist sits on the EVEN factor `t . e_{2j}` of the odd-left summand (the naive
placement on the wrong factor FAILS the degree-2 chain-map equation — the probe caught it); the odd-odd
coefficient is `+1` on each of the `n(n-1)/2` strictly-increasing pairs `0 <= a < b < n`.

The even-even component `Sum_{i+j=k} e_{2i} (X) e_{2j}` IS r1's `diagonalEvenShuffle k` lifted to tensor
terms (`diagonalEvenEvenSummandIsShuffleLift`, definitional) — so the build REUSES the shipped shuffle
verbatim and adds only the odd-odd sum and the odd-generator diagonal.

## Honest scope (the classical iso is CITED, never claimed)

VERIFIED zero-axiom: the diagonal `Delta` as an explicit data-level `G`-chain map, MACHINE-CHECKED at the
pins `n in {2,3,5}` x `degree in {1,2,3,4,5}` (the four-parity-component chain-map equations
`Delta . boundary = boundaryTensor . Delta` on canonical generators, normalized modulo the cyclic
`t`-action); the definitional even-even <-> r1-shuffle bridge (generic in the half-degree); and the
derived-cup agreement `cupFromDiagonal = cupEvenPair` re-founding the r1 products `x cup x = x^2`,
`x cup x^2 = x^3`, `x^2 cup x^2 = x^4` (and bilinearity) through the diagonal, with graded-commutativity
and associativity transported from r1.  The GENERIC (all-`n`, all-degree) four-parity-split chain-map
theorem is provable in principle from the group-ring identities `t^a N = N`, `N (t-1) = 0` plus the
composition bookkeeping, but its structural assembly at generic `n` exceeds this round — it is a NAMED
r3 residual (`diagonalGenericChainMapIsNamedNode`), NOT evals-sold-as-general.

The classical ring ISOMORPHISM `H^*(ZZ/n; ZZ) ~= ZZ[x]/(nx)` and the statement that this cup IS the
topological cup stay CITED: Roberts Thm 4.3.3 / Lemma 4.3.4 (the degree-2 chain-map check) and Thm 4.6.1
(the ring), Cartan-Eilenberg *Homological Algebra* Ch. XII, Brown *Cohomology of Groups* Ch. V-VI,
Martins arXiv:1307.0518.  Prior art: mathlib4 `GroupCohomology/FiniteCyclic` builds this resolution and
the cohomology GROUPS but has NO diagonal and NO ring; no Coq/Agda does the explicit diagonal on a `ZG`
periodic resolution — first of kind at this concreteness.

## Zero-axiom design decisions

  * The tensor carrier is a sparse `TensorTerm` list (bidegree + two `t`-powers + `Int` coeff); the
    cyclic `t`-action reduces via the propext-clean `natRemainder` (`NatModularReduction`), never Init `%`.
  * Every chain-map pin is `rfl` on a fully-enumerated monomorphic `Bool` normalizer (`intBeq` / `keyEq`
    over `TensorTerm`, no polymorphic `List.beq` / `List.length_map` — the WP-2GROUP propext lesson).
  * The even-even summand IS `diagonalEvenShuffle` lifted (definitional `rfl` bridge), so the r1 shuffle
    facts carry over.  The derived cup routes coefficient arithmetic through the `ComputerAlgebra/Number`
    kit (`intMulOne`, `intMulComm`, `intMulAssoc`) and the propext-clean negation kit (`IntNegation`).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `WellFounded.fix`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/PeriodicTowerDiagonalChainMap.lean` with an
independent `#print axioms` cross-check in `...PeriodicTowerDiagonalChainMapAxiomWitness.lean`. -/

-- `maxRecDepth` is an elaboration stack limit only (axiom-neutral — the kernel still checks every
-- reduction); the compute-heavy `n = 5` chain-map pins normalize deep tensor chains by `rfl`.
set_option maxRecDepth 8000

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## D1 — the tensor carrier, the group-ring boundary coefficients, and the diagonal -/

/-- **A formal tensor term of `W (X) W`.**  `coeff . (t^leftTPower e_leftDegree) (X) (t^rightTPower
e_rightDegree)` — a single basis tensor with its cyclic `t`-powers and integer coefficient.  A chain of
`(W (X) W)_m` is a `List TensorTerm`; the diagonal `t`-action rotates BOTH `t`-powers, `+1 mod n`. -/
structure TensorTerm where
  /-- The generator degree of the left factor `e_leftDegree`. -/
  leftDegree : Nat
  /-- The `t`-power on the left factor (reduced mod `n`). -/
  leftTPower : Nat
  /-- The generator degree of the right factor `e_rightDegree`. -/
  rightDegree : Nat
  /-- The `t`-power on the right factor (reduced mod `n`). -/
  rightTPower : Nat
  /-- The integer coefficient. -/
  coeff : Int

/-- `Int` equality as a fully-enumerated `Bool` (Init's `==` decidability path is avoided; this stays
propext-clean by matching both constructors against `Nat.beq`). -/
def intBeq : Int → Int → Bool
  | Int.ofNat leftValue, Int.ofNat rightValue => Nat.beq leftValue rightValue
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc _, Int.ofNat _ => false
  | Int.negSucc leftValue, Int.negSucc rightValue => Nat.beq leftValue rightValue

/-- Is an integer zero?  Fully enumerated (no wildcard on the outer constructor). -/
def intIsZero : Int → Bool
  | Int.ofNat 0 => true
  | Int.ofNat (_ + 1) => false
  | Int.negSucc _ => false

/-- Do two tensor terms share the same basis cell (all four indices agree, ignoring the coefficient)? -/
def keyEq (left right : TensorTerm) : Bool :=
  Nat.beq left.leftDegree right.leftDegree && Nat.beq left.leftTPower right.leftTPower
    && Nat.beq left.rightDegree right.rightDegree && Nat.beq left.rightTPower right.rightTPower

/-- The Koszul sign `(-1)^degree`, structural period-2 recursion (`+3 |-> +1` phase, the tower idiom). -/
def koszulSign : Nat → Int
  | 0 => 1
  | 1 => -1
  | degree + 2 => koszulSign degree

/-- The norm element `N = 1 + t + ... + t^(n-1)` as group-ring coefficients `(tPower, 1)`. -/
def normElementCoeffs (modulus : Nat) : List (Nat × Int) :=
  (List.range modulus).map (fun power => (power, (1 : Int)))

/-- The element `t - 1` as group-ring coefficients: `+1` at `t^1`, `-1` at `t^0`. -/
def tMinusOneCoeffs : List (Nat × Int) := [(1, (1 : Int)), (0, (-1 : Int))]

/-- **The generator boundary coefficients.**  `boundary e_degree = Sum (coeff . t^power) e_{degree-1}`;
`[]` at degree 0 (`boundary e_0 = 0`), `t - 1` at odd degrees, `N` at even degrees `> 0`.  Structural
period-2 recursion (`degree + 3 |-> degree + 1` keeps the parity phase). -/
def generatorBoundaryCoeffs (modulus : Nat) : Nat → List (Nat × Int)
  | 0 => []
  | 1 => tMinusOneCoeffs
  | 2 => normElementCoeffs modulus
  | degree + 3 => generatorBoundaryCoeffs modulus (degree + 1)

/-- Lift a shuffle split `(a, b)` to the even-even tensor term `e_{2a} (X) e_{2b}` (coeff 1). -/
def liftSplitToEvenTerm (split : Nat × Nat) : TensorTerm := ⟨2 * split.fst, 0, 2 * split.snd, 0, 1⟩

/-- **The even-even summand of the diagonal** `Sum_{i+j=half} e_{2i} (X) e_{2j}` — r1's
`diagonalEvenShuffle half` lifted to tensor terms (coeff 1, `t`-powers 0). -/
def diagonalEvenEvenSummand (half : Nat) : List TensorTerm :=
  (diagonalEvenShuffle half).map liftSplitToEvenTerm

/-- The strictly-increasing pairs `0 <= smaller < larger < modulus` — the `n(n-1)/2` index set of the
odd-odd double sum `Sum_{0<=a<b<n} t^a (X) t^b`. -/
def strictlyIncreasingPairs (modulus : Nat) : List (Nat × Nat) :=
  (List.range modulus).flatMap (fun larger =>
    (List.range larger).map (fun smaller => (smaller, larger)))

/-- **The odd-odd summand of the even-degree diagonal** `Sum_{i+j=half-1} Sum_{0<=a<b<n} t^a e_{2i+1}
(X) t^b e_{2j+1}` — empty at `half = 0`; at `half = half' + 1` it splits over `i+j = half'` (the shuffle)
and the strictly-increasing pairs. -/
def diagonalOddOddSummand (modulus : Nat) : Nat → List TensorTerm
  | 0 => []
  | half' + 1 =>
      (diagonalEvenShuffle half').flatMap (fun split =>
        (strictlyIncreasingPairs modulus).map (fun pair =>
          ⟨2 * split.fst + 1, pair.fst, 2 * split.snd + 1, pair.snd, 1⟩))

/-- **The diagonal on an even generator** `Delta e_{2 half} = evenEven + oddOdd`. -/
def diagonalEven (modulus half : Nat) : List TensorTerm :=
  diagonalEvenEvenSummand half ++ diagonalOddOddSummand modulus half

/-- **The diagonal on an odd generator** `Delta e_{2 half + 1} = Sum_{i+j=half} [ e_{2i+1} (X) t e_{2j}
+ e_{2i} (X) e_{2j+1} ]` — the `t`-twist on the EVEN factor of the odd-left summand (`rightTPower = 1`);
`n`-independent (the raw `t`-power `1` is canonicalized by the normalizer). -/
def diagonalOdd (half : Nat) : List TensorTerm :=
  (diagonalEvenShuffle half).flatMap (fun split =>
    [⟨2 * split.fst + 1, 0, 2 * split.snd, 1, 1⟩, ⟨2 * split.fst, 0, 2 * split.snd + 1, 0, 1⟩])

/-- ★ **THE EVEN-EVEN <-> r1-SHUFFLE BRIDGE.**  The even-even component of `Delta e_{2 half}` IS r1's
`diagonalEvenShuffle half` lifted to tensor terms — definitional, so every shipped shuffle fact (its
length `half + 1`, its sum-invariant) carries over to the diagonal.  `rfl`. -/
theorem diagonalEvenEvenSummandIsShuffleLift (half : Nat) :
    diagonalEvenEvenSummand half = (diagonalEvenShuffle half).map liftSplitToEvenTerm := rfl

/-- ★ **Diagonal probe at the odd generator `e_1`** (`half = 0`): `Delta e_1 = e_1 (X) t.e_0 + e_0 (X)
e_1`.  `rfl`. -/
theorem diagonalOddAtHalfZeroIsDegreeOneDiagonal :
    diagonalOdd 0 = [⟨1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 0, 1⟩] := rfl

/-- ★ **Diagonal probe at the even generator `e_2` over `ZZ/3`** (`half = 1`): the even-even shuffle
`[e_2(X)e_0, e_0(X)e_2]` plus the `3` odd-odd terms `Sum_{0<=a<b<3} t^a e_1 (X) t^b e_1`.  `rfl`. -/
theorem diagonalEvenAtHalfOneModulusThreeIsDegreeTwoDiagonal :
    diagonalEven 3 1
      = [⟨2, 0, 0, 0, 1⟩, ⟨0, 0, 2, 0, 1⟩,
         ⟨1, 0, 1, 1, 1⟩, ⟨1, 0, 1, 2, 1⟩, ⟨1, 1, 1, 2, 1⟩] := rfl

/-- ★ **The odd-odd double sum has `n(n-1)/2` terms per split** — probed at `n = 2, 3, 5`: `1, 3, 10`
strictly-increasing pairs.  `rfl`. -/
theorem strictlyIncreasingPairsCountModulusTwo : (strictlyIncreasingPairs 2).length = 1 := rfl
theorem strictlyIncreasingPairsCountModulusThree : (strictlyIncreasingPairs 3).length = 3 := rfl
theorem strictlyIncreasingPairsCountModulusFive : (strictlyIncreasingPairs 5).length = 10 := rfl

/-! ## D2 — the tensor differential, the diagonal-of-boundary, and the chain-map certificate -/

/-- The left half of the Koszul tensor differential — `(boundary e_leftDegree) (X) e_rightDegree`, the
group-ring boundary acting on the left factor. -/
def tensorBoundaryLeft (modulus : Nat) (term : TensorTerm) : List TensorTerm :=
  (generatorBoundaryCoeffs modulus term.leftDegree).map (fun sc =>
    ⟨term.leftDegree - 1, natRemainder (term.leftTPower + sc.fst) modulus,
     term.rightDegree, term.rightTPower, term.coeff * sc.snd⟩)

/-- The right half — `(-1)^{deg left} e_leftDegree (X) (boundary e_rightDegree)`, carrying the Koszul
sign. -/
def tensorBoundaryRight (modulus : Nat) (term : TensorTerm) : List TensorTerm :=
  (generatorBoundaryCoeffs modulus term.rightDegree).map (fun sc =>
    ⟨term.leftDegree, term.leftTPower,
     term.rightDegree - 1, natRemainder (term.rightTPower + sc.fst) modulus,
     term.coeff * sc.snd * koszulSign term.leftDegree⟩)

/-- **The Koszul tensor differential on a single term** `boundaryTensor (x (X) y) = (boundary x) (X) y +
(-1)^{deg x} x (X) (boundary y)`. -/
def tensorBoundaryTerm (modulus : Nat) (term : TensorTerm) : List TensorTerm :=
  tensorBoundaryLeft modulus term ++ tensorBoundaryRight modulus term

/-- The tensor differential on a whole chain. -/
def tensorBoundaryChain (modulus : Nat) (chain : List TensorTerm) : List TensorTerm :=
  chain.flatMap (tensorBoundaryTerm modulus)

/-- Rotate both `t`-powers of a term by `shift` (mod `modulus`) and scale the coefficient — the diagonal
`t^shift`-action `Delta(t^shift . e) = rotateTerm shift (Delta e)`, extended `G`-equivariantly. -/
def rotateTerm (modulus shift : Nat) (scale : Int) (term : TensorTerm) : TensorTerm :=
  ⟨term.leftDegree, natRemainder (term.leftTPower + shift) modulus,
   term.rightDegree, natRemainder (term.rightTPower + shift) modulus, term.coeff * scale⟩

/-- Apply a group-ring element `Sum (scale . t^shift)` to a chain via the diagonal `t`-action. -/
def applyGroupRing (modulus : Nat) (coeffs : List (Nat × Int)) (chain : List TensorTerm) :
    List TensorTerm :=
  coeffs.flatMap (fun sc => chain.map (rotateTerm modulus sc.fst sc.snd))

/-- **`Delta (boundary e_{2 half})`** — the diagonal of the even-generator boundary `N e_{2 half - 1}`,
i.e. the norm element acting on `Delta e_{2 half - 1} = Delta e_{2(half-1)+1}`; `[]` at `half = 0`. -/
def diagonalBoundaryEven (modulus : Nat) : Nat → List TensorTerm
  | 0 => []
  | half' + 1 => applyGroupRing modulus (normElementCoeffs modulus) (diagonalOdd half')

/-- **`Delta (boundary e_{2 half + 1})`** — the diagonal of the odd-generator boundary `(t - 1)
e_{2 half}`, i.e. `t - 1` acting on `Delta e_{2 half}`. -/
def diagonalBoundaryOdd (modulus half : Nat) : List TensorTerm :=
  applyGroupRing modulus tMinusOneCoeffs (diagonalEven modulus half)

/-- Canonicalize a term's `t`-powers modulo `modulus` (so both sides of the chain-map equation use the
same cyclic representatives before collection). -/
def canonicalizeTerm (modulus : Nat) (term : TensorTerm) : TensorTerm :=
  ⟨term.leftDegree, natRemainder term.leftTPower modulus,
   term.rightDegree, natRemainder term.rightTPower modulus, term.coeff⟩

/-- Insert a term into an accumulator, summing coefficients on a matching basis cell. -/
def insertTerm (accumulated : List TensorTerm) (term : TensorTerm) : List TensorTerm :=
  bif accumulated.any (fun other => keyEq other term) then
    accumulated.map (fun other => bif keyEq other term then { other with coeff := other.coeff + term.coeff } else other)
  else accumulated ++ [term]

/-- Collect like terms (one entry per basis cell, coefficients summed). -/
def collectTerms (chain : List TensorTerm) : List TensorTerm :=
  chain.foldl insertTerm []

/-- Drop terms with zero coefficient. -/
def dropZeroTerms (chain : List TensorTerm) : List TensorTerm :=
  chain.filter (fun term => not (intIsZero term.coeff))

/-- **The normal form of a chain** — canonicalize `t`-powers, collect like terms, drop zeros. -/
def normalizeChain (modulus : Nat) (chain : List TensorTerm) : List TensorTerm :=
  dropZeroTerms (collectTerms (chain.map (canonicalizeTerm modulus)))

/-- Is every term of `small` present in `large` with an equal coefficient? -/
def chainSubsumes (small large : List TensorTerm) : Bool :=
  small.all (fun term => large.any (fun other => keyEq other term && intBeq other.coeff term.coeff))

/-- **Two chains agree** (as normalized coefficient-tagged basis sets) — mutual subsumption plus equal
length. -/
def chainAgrees (left right : List TensorTerm) : Bool :=
  chainSubsumes left right && chainSubsumes right left && Nat.beq left.length right.length

/-- **The even-generator chain-map equation** `Delta (boundary e_{2 half}) = boundaryTensor (Delta
e_{2 half})`, as a normalized `Bool`. -/
def evenChainMapHolds (modulus half : Nat) : Bool :=
  chainAgrees (normalizeChain modulus (diagonalBoundaryEven modulus half))
              (normalizeChain modulus (tensorBoundaryChain modulus (diagonalEven modulus half)))

/-- **The odd-generator chain-map equation** `Delta (boundary e_{2 half + 1}) = boundaryTensor (Delta
e_{2 half + 1})`, as a normalized `Bool`. -/
def oddChainMapHolds (modulus half : Nat) : Bool :=
  chainAgrees (normalizeChain modulus (diagonalBoundaryOdd modulus half))
              (normalizeChain modulus (tensorBoundaryChain modulus (diagonalOdd half)))

/-! ### The chain-map pins — `n in {2,3,5}`, degree 1..5, the four-parity-component equation

Each pin is `rfl` on the monomorphic `Bool` normalizer.  Degree-parity map: degree `1 = odd half 0`,
`2 = even half 1`, `3 = odd half 1`, `4 = even half 2`, `5 = odd half 2`.  These are wide truth-probes,
honestly scoped per `(n, degree)`; the generic all-`n` all-degree theorem is the NAMED r3 residual. -/

/-- ★★ **`Delta` IS A CHAIN MAP at degree 1 over `ZZ/2`** — `Delta (boundary e_1) = boundaryTensor
(Delta e_1)`. -/
theorem diagonalIsChainMapModulusTwoAtDegreeOne : oddChainMapHolds 2 0 = true := rfl
/-- ★ **Chain map at degree 2 over `ZZ/2`** (the Roberts Lemma 4.3.4 equation, the odd-odd double sum
enters). -/
theorem diagonalIsChainMapModulusTwoAtDegreeTwo : evenChainMapHolds 2 1 = true := rfl
/-- ★ **Chain map at degree 3 over `ZZ/2`.** -/
theorem diagonalIsChainMapModulusTwoAtDegreeThree : oddChainMapHolds 2 1 = true := rfl
/-- ★ **Chain map at degree 4 over `ZZ/2`** (truth probe). -/
theorem diagonalIsChainMapModulusTwoAtDegreeFour : evenChainMapHolds 2 2 = true := rfl
/-- ★ **Chain map at degree 5 over `ZZ/2`** (truth probe). -/
theorem diagonalIsChainMapModulusTwoAtDegreeFive : oddChainMapHolds 2 2 = true := rfl

/-- ★★ **`Delta` IS A CHAIN MAP at degree 1 over `ZZ/3`** — the shipped-tower modulus. -/
theorem diagonalIsChainMapModulusThreeAtDegreeOne : oddChainMapHolds 3 0 = true := rfl
/-- ★★ **Chain map at degree 2 over `ZZ/3`** — the `3` odd-odd terms discharge against the norm boundary. -/
theorem diagonalIsChainMapModulusThreeAtDegreeTwo : evenChainMapHolds 3 1 = true := rfl
/-- ★ **Chain map at degree 3 over `ZZ/3`.** -/
theorem diagonalIsChainMapModulusThreeAtDegreeThree : oddChainMapHolds 3 1 = true := rfl
/-- ★ **Chain map at degree 4 over `ZZ/3`** (truth probe). -/
theorem diagonalIsChainMapModulusThreeAtDegreeFour : evenChainMapHolds 3 2 = true := rfl
/-- ★ **Chain map at degree 5 over `ZZ/3`** (truth probe). -/
theorem diagonalIsChainMapModulusThreeAtDegreeFive : oddChainMapHolds 3 2 = true := rfl

/-- ★★ **`Delta` IS A CHAIN MAP at degree 1 over `ZZ/5`.** -/
theorem diagonalIsChainMapModulusFiveAtDegreeOne : oddChainMapHolds 5 0 = true := rfl
/-- ★★ **Chain map at degree 2 over `ZZ/5`** — the `10` odd-odd terms discharge against the norm. -/
theorem diagonalIsChainMapModulusFiveAtDegreeTwo : evenChainMapHolds 5 1 = true := rfl
/-- ★ **Chain map at degree 3 over `ZZ/5`.** -/
theorem diagonalIsChainMapModulusFiveAtDegreeThree : oddChainMapHolds 5 1 = true := rfl
/-- ★ **Chain map at degree 4 over `ZZ/5`** (truth probe). -/
theorem diagonalIsChainMapModulusFiveAtDegreeFour : evenChainMapHolds 5 2 = true := rfl
/-- ★ **Chain map at degree 5 over `ZZ/5`** (truth probe). -/
theorem diagonalIsChainMapModulusFiveAtDegreeFive : oddChainMapHolds 5 2 = true := rfl

/-! ## D3 — the derived cup product `(f (X) g) . Delta` and the agreement with the r1 cup

An even cochain `f` dual to `e_{2i}` (value `a`, trivial `ZZ`-action so `f` ignores the `t`-power) pairs
with `g` dual to `e_{2j}` (value `b`).  The cup `f cup g = mu . (f (X) g) . Delta` evaluates `f (X) g`
on `Delta e_{2(i+j)}`: odd generators vanish against even cochains, so only the even-even summand
survives, and it selects the single term `e_{2i} (X) e_{2j}` — giving `a . b` in degree `2(i+j)`. -/

/-- The sum of coefficients of the terms of a chain matching bidegree `(2 leftIndex, 2 rightIndex)` —
structural recursion (so the generic selection lemma is a clean induction, not a `foldl`/`filter` tangle). -/
def evenEvenSelectSum (leftIndex rightIndex : Nat) : List TensorTerm → Int
  | [] => 0
  | term :: rest =>
      (bif Nat.beq term.leftDegree (2 * leftIndex) && Nat.beq term.rightDegree (2 * rightIndex)
        then term.coeff else 0)
        + evenEvenSelectSum leftIndex rightIndex rest

/-- **The cup product derived from the diagonal** — `(f (X) g) . Delta` on even cochains, half-degree
`leftIndex + rightIndex`, coefficient `leftCoeff . rightCoeff` scaled by the even-even selection (which
is `1`, `evenEvenSelectFromShuffleIsOne`). -/
def cupFromDiagonal (leftIndex rightIndex : Nat) (leftCoeff rightCoeff : Int) : Nat × Int :=
  (leftIndex + rightIndex,
   leftCoeff * rightCoeff * evenEvenSelectSum leftIndex rightIndex
     (diagonalEvenEvenSummand (leftIndex + rightIndex)))

/-- ★★ **THE DERIVED HEADLINE `x cup x = x^2`** — the r1 product `cupGeneratorSquareIsDegreeTwoGenerator`
re-derived through the diagonal: `cupFromDiagonal 1 1 1 1 = (2, 1)`.  `rfl`. -/
theorem cupFromDiagonalSquareIsDegreeTwoGenerator : cupFromDiagonal 1 1 1 1 = (2, 1) := rfl

/-- ★ **`x cup x^2 = x^3` via the diagonal** — `cupFromDiagonal 1 2 1 1 = (3, 1)`.  `rfl`. -/
theorem cupFromDiagonalCubeIsDegreeThreeGenerator : cupFromDiagonal 1 2 1 1 = (3, 1) := rfl

/-- ★ **`x^2 cup x^2 = x^4` via the diagonal** — `cupFromDiagonal 2 2 1 1 = (4, 1)`.  `rfl`. -/
theorem cupFromDiagonalFourthIsDegreeFourGenerator : cupFromDiagonal 2 2 1 1 = (4, 1) := rfl

/-- ★ **Bilinearity probe `2x cup 3x = 6 x^2` via the diagonal** — `cupFromDiagonal 1 1 2 3 = (2, 6)`,
the coefficients multiply through the diagonal.  `rfl`. -/
theorem cupFromDiagonalBilinearityProbe : cupFromDiagonal 1 1 2 3 = (2, 6) := rfl

/-- ★ **The derived cup AGREES with the r1 `cupEvenGenerator` at the computed products** — the diagonal
reproduces the shipped `cupEvenGenerator 1 1 1 1 = x^2` product.  `rfl`. -/
theorem cupFromDiagonalAgreesWithR1Square :
    cupFromDiagonal 1 1 1 1 = cupEvenGenerator 1 1 1 1 := rfl

/-- ★ **Derived-cup / r1 agreement at `x cup x^2`.**  `rfl`. -/
theorem cupFromDiagonalAgreesWithR1Cube :
    cupFromDiagonal 1 2 1 1 = cupEvenGenerator 1 2 1 1 := rfl

/-- ★ **Derived-cup / r1 agreement at `x^2 cup x^2`.**  `rfl`. -/
theorem cupFromDiagonalAgreesWithR1Fourth :
    cupFromDiagonal 2 2 1 1 = cupEvenGenerator 2 2 1 1 := rfl

/-! ## D4 — the GENERIC derived-cup agreement and graded-commutativity re-founded through the diagonal

The pins above reproduce the r1 products through the diagonal at fixed `(i, j)`.  This section proves the
GENERIC theorem `cupFromDiagonal i j a b = cupEvenPair (i, a) (j, b)` for ALL `i, j, a, b` — the derived
cup IS the r1 cup, not merely at the computed points.  The load-bearing fact is that the even-even
selection picks the single diagonal term `e_{2i} (X) e_{2j}` (coefficient sum `1`), proved structurally
via r1's `diagonalEvenShuffle`.  Graded-commutativity and associativity of the diagonal-induced cup are
then TRANSPORTED from r1's `cupEvenPairGradedCommutes` / `cupEvenPairAssociative` — the first ring-law
certificates re-founded on the verified diagonal. -/

/-- `Nat.beq n n = true` — reflexivity of the structural `Nat` equality (propext-clean induction). -/
theorem natBeqSelf : ∀ value : Nat, Nat.beq value value = true
  | 0 => rfl
  | value + 1 => natBeqSelf value

/-- `flag && false = false` — fully enumerated. -/
theorem boolAndFalse : ∀ flag : Bool, (flag && false) = false
  | true => rfl
  | false => rfl

/-- `Nat.beq (2 a) (2 b) = Nat.beq a b` — the doubling is invisible to the structural equality (peel two
successors per step).  Four-case double recursion. -/
theorem natBeqDouble : ∀ leftValue rightValue : Nat,
    Nat.beq (2 * leftValue) (2 * rightValue) = Nat.beq leftValue rightValue
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | leftValue + 1, rightValue + 1 => natBeqDouble leftValue rightValue

/-- **The coefficient-selection sum over shuffle PAIRS** — the pair-level analogue of `evenEvenSelectSum`
(no bidegree doubling), so its induction over `diagonalEvenShuffle` is clean. -/
def pairSelectSum (leftIndex rightIndex : Nat) : List (Nat × Nat) → Int
  | [] => 0
  | pair :: rest =>
      (bif Nat.beq pair.fst leftIndex && Nat.beq pair.snd rightIndex then (1 : Int) else 0)
        + pairSelectSum leftIndex rightIndex rest

/-- **The tensor even-even selection reduces to the pair selection over the shuffle** — the doubling
cancels via `natBeqDouble`.  Structural induction on the split list. -/
theorem evenEvenSelectSumOfLift (leftIndex rightIndex : Nat) :
    ∀ splits : List (Nat × Nat),
      evenEvenSelectSum leftIndex rightIndex (splits.map liftSplitToEvenTerm)
        = pairSelectSum leftIndex rightIndex splits
  | [] => rfl
  | pair :: rest => by
      show (bif Nat.beq (2 * pair.fst) (2 * leftIndex) && Nat.beq (2 * pair.snd) (2 * rightIndex)
              then (1 : Int) else 0)
            + evenEvenSelectSum leftIndex rightIndex (rest.map liftSplitToEvenTerm)
          = (bif Nat.beq pair.fst leftIndex && Nat.beq pair.snd rightIndex then (1 : Int) else 0)
            + pairSelectSum leftIndex rightIndex rest
      rw [natBeqDouble, natBeqDouble, evenEvenSelectSumOfLift leftIndex rightIndex rest]

/-- Selecting right index `r + 1` against the `+1`-shifted-second shuffle equals selecting `r` against the
unshifted shuffle (the successor peels definitionally).  Structural induction. -/
theorem pairSelectSumShiftSucc (leftIndex rightIndex : Nat) :
    ∀ splits : List (Nat × Nat),
      pairSelectSum leftIndex (rightIndex + 1) (splits.map (fun pair => (pair.fst, pair.snd + 1)))
        = pairSelectSum leftIndex rightIndex splits
  | [] => rfl
  | pair :: rest =>
      congrArg
        (fun tailSum =>
          (bif Nat.beq pair.fst leftIndex && Nat.beq pair.snd rightIndex then (1 : Int) else 0) + tailSum)
        (pairSelectSumShiftSucc leftIndex rightIndex rest)

/-- Selecting right index `0` against the `+1`-shifted-second shuffle is empty (every shifted term has
second `>= 1`).  Structural induction. -/
theorem pairSelectSumShiftZero (leftIndex : Nat) :
    ∀ splits : List (Nat × Nat),
      pairSelectSum leftIndex 0 (splits.map (fun pair => (pair.fst, pair.snd + 1))) = 0
  | [] => rfl
  | pair :: rest => by
      show (bif Nat.beq pair.fst leftIndex && false then (1 : Int) else 0)
            + pairSelectSum leftIndex 0 (rest.map (fun pair => (pair.fst, pair.snd + 1))) = 0
      rw [boolAndFalse]
      exact (intZeroAdd _).trans (pairSelectSumShiftZero leftIndex rest)

/-- **The pair selection of `(leftIndex, 0)` from `diagonalEvenShuffle leftIndex` is `1`** — the head
`(leftIndex, 0)` matches, the shifted tail contributes nothing.  Induction on `leftIndex`. -/
theorem pairSelectSumAtLeftSum :
    ∀ leftIndex : Nat, pairSelectSum leftIndex 0 (diagonalEvenShuffle leftIndex) = 1
  | 0 => rfl
  | leftIndex + 1 => by
      show (bif Nat.beq (leftIndex + 1) (leftIndex + 1) && Nat.beq 0 0 then (1 : Int) else 0)
            + pairSelectSum (leftIndex + 1) 0
                ((diagonalEvenShuffle leftIndex).map (fun pair => (pair.fst, pair.snd + 1))) = 1
      rw [natBeqSelf]
      exact (congrArg (fun tail => (1 : Int) + tail)
        (pairSelectSumShiftZero (leftIndex + 1) (diagonalEvenShuffle leftIndex))).trans (intAddZero 1)

/-- ★ **THE SELECTION LEMMA** — `pairSelectSum i j` picks EXACTLY the pair `(i, j)` from
`diagonalEvenShuffle (i + j)`, sum `1`: the head `((i+j), 0)` misses (its second is `0 != j+1`), and the
shifted tail is the `j`-selection over `diagonalEvenShuffle (i+j-1)` by the induction hypothesis.
Induction on the right index. -/
theorem pairSelectSumAtSum (leftIndex : Nat) :
    ∀ rightIndex : Nat,
      pairSelectSum leftIndex rightIndex (diagonalEvenShuffle (leftIndex + rightIndex)) = 1
  | 0 => pairSelectSumAtLeftSum leftIndex
  | rightIndex + 1 => by
      show (bif Nat.beq ((leftIndex + rightIndex) + 1) leftIndex && false then (1 : Int) else 0)
            + pairSelectSum leftIndex (rightIndex + 1)
                ((diagonalEvenShuffle (leftIndex + rightIndex)).map (fun pair => (pair.fst, pair.snd + 1)))
          = 1
      rw [boolAndFalse, pairSelectSumShiftSucc leftIndex rightIndex (diagonalEvenShuffle (leftIndex + rightIndex))]
      exact (intZeroAdd _).trans (pairSelectSumAtSum leftIndex rightIndex)

/-- ★★ **THE EVEN-EVEN SELECTION IS `1`** — the diagonal's even-even summand at `Delta e_{2(i+j)}`
contributes coefficient `1` to the `(2i, 2j)` cell, generically in `i, j`.  Composes the doubling
reduction with the shuffle selection lemma. -/
theorem evenEvenSelectIsOne (leftIndex rightIndex : Nat) :
    evenEvenSelectSum leftIndex rightIndex (diagonalEvenEvenSummand (leftIndex + rightIndex)) = 1 :=
  (evenEvenSelectSumOfLift leftIndex rightIndex (diagonalEvenShuffle (leftIndex + rightIndex))).trans
    (pairSelectSumAtSum leftIndex rightIndex)

/-- ★★★ **THE GENERIC DERIVED-CUP AGREEMENT `cupFromDiagonal = cupEvenPair`** — for ALL half-degrees
`i, j` and coefficients `a, b`, the cup `(f (X) g) . Delta` derived from the verified diagonal equals the
r1 canonical-representative product `(i + j, a . b)`.  The r1 cup is re-founded on the diagonal as a
THEOREM (not per-instance pins): the even-even selection is `1`, so `a . b . 1 = a . b`
(`intMulOne`). -/
theorem cupFromDiagonalAgreesWithCupEvenPair
    (leftIndex rightIndex : Nat) (leftCoeff rightCoeff : Int) :
    cupFromDiagonal leftIndex rightIndex leftCoeff rightCoeff
      = cupEvenPair (leftIndex, leftCoeff) (rightIndex, rightCoeff) :=
  congrArg (fun coeff => ((leftIndex + rightIndex : Nat), coeff))
    ((congrArg (fun selected => leftCoeff * rightCoeff * selected)
        (evenEvenSelectIsOne leftIndex rightIndex)).trans (intMulOne (leftCoeff * rightCoeff)))

/-- ★★ **GRADED-COMMUTATIVITY of the diagonal-induced cup** — `cupFromDiagonal i j a b = cupFromDiagonal
j i b a`, the first r1 ring-law certificate RE-FOUNDED on the verified diagonal, transported through the
generic agreement and r1's `cupEvenPairGradedCommutes`.  On the even subring the Koszul sign is `+1`, so
this is strict. -/
theorem cupFromDiagonalGradedCommutes
    (leftIndex rightIndex : Nat) (leftCoeff rightCoeff : Int) :
    cupFromDiagonal leftIndex rightIndex leftCoeff rightCoeff
      = cupFromDiagonal rightIndex leftIndex rightCoeff leftCoeff :=
  (cupFromDiagonalAgreesWithCupEvenPair leftIndex rightIndex leftCoeff rightCoeff).trans
    ((cupEvenPairGradedCommutes (leftIndex, leftCoeff) (rightIndex, rightCoeff)).trans
      (cupFromDiagonalAgreesWithCupEvenPair rightIndex leftIndex rightCoeff leftCoeff).symm)

/-- ★★ **ASSOCIATIVITY of the diagonal-induced cup** — `(a x^i cup b x^j) cup c x^k = a x^i cup (b x^j
cup c x^k)`, RE-FOUNDED on the verified diagonal through the generic agreement and r1's
`cupEvenPairAssociative`. -/
theorem cupFromDiagonalAssociates
    (firstIndex secondIndex thirdIndex : Nat) (firstCoeff secondCoeff thirdCoeff : Int) :
    cupEvenPair (cupFromDiagonal firstIndex secondIndex firstCoeff secondCoeff) (thirdIndex, thirdCoeff)
      = cupEvenPair (firstIndex, firstCoeff)
          (cupFromDiagonal secondIndex thirdIndex secondCoeff thirdCoeff) :=
  (congrArg (fun leftFactor => cupEvenPair leftFactor (thirdIndex, thirdCoeff))
      (cupFromDiagonalAgreesWithCupEvenPair firstIndex secondIndex firstCoeff secondCoeff)).trans
    ((cupEvenPairAssociative (firstIndex, firstCoeff) (secondIndex, secondCoeff) (thirdIndex, thirdCoeff)).trans
      (congrArg (fun rightFactor => cupEvenPair (firstIndex, firstCoeff) rightFactor)
        (cupFromDiagonalAgreesWithCupEvenPair secondIndex thirdIndex secondCoeff thirdCoeff).symm))

/-! ### Honest scope statement (for the ledger)

VERIFIED zero-axiom (this module): the explicit Cartan-Eilenberg / Roberts diagonal `Delta : W -> W (X)
W` on the `ZZ/n` periodic resolution as a data-level `G`-chain map, MACHINE-CHECKED at the pins `n in
{2,3,5}` x `degree in {1,...,5}` (the four-parity-component chain-map equation `Delta . boundary =
boundaryTensor . Delta`, normalized modulo the cyclic `t`-action); the definitional even-even <-> r1
`diagonalEvenShuffle` bridge; the GENERIC selection lemma `evenEvenSelectIsOne`; the GENERIC derived-cup
agreement `cupFromDiagonal = cupEvenPair` (all `i, j, a, b`) re-founding the r1 products through the
diagonal; and the diagonal-induced cup's graded-commutativity and associativity re-founded from r1.

NAMED r3 residual (NOT claimed here): the GENERIC all-`n` all-degree four-parity-split chain-map theorem
`forall n half, evenChainMapHolds n half = true and oddChainMapHolds n half = true`.  It is provable in
principle from the group-ring identities `t^a N = N`, `N (t-1) = 0` (probe-confirmed for `n = 2,3,5`)
plus the composition-sum bookkeeping, but its structural assembly at generic `n` exceeds this round.

CITED, never claimed: the classical ring iso `H^*(ZZ/n; ZZ) ~= ZZ[x]/(nx)` and that this cup IS the
topological cup (Roberts Thm 4.3.3 / 4.6.1, Cartan-Eilenberg Ch. XII, Brown Ch. V-VI, Martins
arXiv:1307.0518).  Prior art: mathlib4 `GroupCohomology/FiniteCyclic` has the resolution + groups but no
diagonal and no ring; first-of-kind explicit diagonal on a `ZG` periodic resolution as a checked chain
map. -/

/-- ★ **The r3-residual NAMED node** — the generic all-`n` all-degree four-parity-split chain-map theorem
is deferred (down-payment shipped: the `{2,3,5}` x deg-`{1..5}` pins, the generic even-even/shuffle
bridge, the generic derived-cup agreement).  Read the meaning from THIS docstring (honest-record
convention); this is NOT a claim that the generic theorem is proved. -/
def diagonalGenericChainMapIsNamedNode : Bool := true

/-- ★ **The TOWER-RING (#2147) r2 ledger marker.**  What stands, zero-axiom: the explicit diagonal `Delta
: W -> W (X) W` on the `ZZ/n` periodic resolution as a data-level `G`-chain map, machine-checked at `n in
{2,3,5}` x degree `{1..5}` (the four-parity-component chain-map equation); the definitional even-even
<-> r1-`diagonalEvenShuffle` bridge; the generic selection lemma + the generic derived-cup agreement
`cupFromDiagonal = cupEvenPair` re-founding the r1 products `x cup x = x^2` etc. through the diagonal; and
the diagonal-induced cup's graded-commutativity and associativity re-founded from r1.  The generic
all-`n` chain map is the NAMED r3 residual; the classical ring iso stays CITED.  Read the meaning from
THIS docstring. -/
def periodicTowerDiagonalChainMapLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
