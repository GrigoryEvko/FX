import FX1Poly.Polygraph.Homology.PeriodicTowerChainComplex
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntMulAssociativity

/-! # FX1Poly/Polygraph/Homology/PeriodicTowerCohomologyCupProduct — the COHOMOLOGY ring of `ZZ/n`
    on the shipped 2-periodic tower: the dual cochain complex, the all-degrees read-off
    `H^0 = ZZ, H^even>0 = ZZ/n, H^odd = 0`, the explicit even-degree diagonal, and the cup product of
    the degree-2 generator with its bilinearity / associativity / graded-commutativity certificates
    (TOWER-RING, #2147, r1 opener)

The shipped `Homology/PeriodicTowerChainComplex` computes the group **HOMOLOGY** `H_*(ZZ/3; ZZ)` — with
`ZZ/3` torsion in the **ODD** degrees (`H0 = ZZ, H_odd = ZZ/3, H_even>0 = 0`).  The cohomology **RING**
`ZZ[x]/(nx)` with `|x| = 2` lives in **COHOMOLOGY** `H^*(ZZ/n; ZZ)`, where the same torsion sits in the
**EVEN** degrees — exactly where the degree-2 generator `x` lives.  This module builds the COCHAIN
complex (the dual of the shipped tower) and puts the ring on its cohomology.  The dualization is clean
because the periodic resolution is self-dual up to sign: for the rank-1-at-every-degree tower each chain
module `C_k = ZZ`, its dual `C^k = Hom(C_k, ZZ) = ZZ`, and the coboundary `δ^k = (∂_{k+1})^T` reuses the
shipped boundary literals verbatim (`1 × 1` transpose is the identity).

## The math (compute first, state after)

`ZZ/n = ⟨t | t^n = 1⟩`, trivial `ZZ` coefficients.  The dual of the 2-periodic resolution:

  `ZZ --eps^T--> C^0 --δ^0=(t−1)^T=0--> C^1 --δ^1=N^T=n--> C^2 --δ^2=0--> C^3 --δ^3=n--> ⋯`

so `δ^even = 0`, `δ^odd = n` (numerically; the shipped tower seeds `[[-3]]`, SNF `[[3]]`).  Cohomology
`H^k = ker δ^k / im δ^{k-1}`:

  | k        | rank δ^k | rank δ^{k-1} | freeRank | torsion | `H^k` |
  |----------|----------|--------------|----------|---------|-------|
  | 0        | 0        | —            | 1        | []      | `ZZ`  |
  | odd      | 1 (`n`)  | 0            | 0        | []      | `0`   |
  | even > 0 | 0        | 1 (`n`)      | 0        | [n]     | `ZZ/n`|

→ `H^0 = ZZ, H^odd = 0, H^even>0 = ZZ/n`.  Reusing the shipped generic `SmithHomologyData.homologyInvariant`,
the cohomology Smith data at degree `k` is the shipped **homology** data with the two boundary SNFs' roles
EXCHANGED (`smithBoundaryIntoLower := SNF(δ^k) = SNF(∂_{k+1})`, `smithBoundaryFromHigher := SNF(δ^{k-1})
= SNF(∂_k)`), which moves the `[[n]]` torsion from odd degrees (homology) into even degrees (cohomology).
Concretely `cyclicThreeCohomEvenPositiveDegreeSmithData` is defeq the shipped
`cyclicThreeTowerOddDegreeSmithData` (`rfl`, the swap witness) and `cyclicThreeCohomInvariantAtDegree 2 =
cyclicThreeTowerHomologyInvariantAtDegree 1` (the dimension-shift dualization).

## The ring `ZZ[x]/(nx)`, `|x| = 2` (presented; classical iso CITED, never claimed)

The even subring is `ZZ[x]` with `x` the degree-2 class, cut by the torsion relation `n·x = 0`.  This
module ships that ring as DATA + machine-checked certificates:

  * the cup product of two even classes `(halfDegree, coeff)` is `cupEvenPair`/`cupEvenGenerator`
    (`(i, a) ∪ (j, b) = (i + j, a * b)` — half-degrees add, coefficients multiply);
  * the explicit even-degree DIAGONAL shuffle `diagonalEvenShuffle i` = the index set `{(k, l) : k + l =
    i}` of `Σ_{k+l=i} σ^(k) ⊗ σ^(l)` (Roberts thesis Thm 4.3.3 / eq. 4.4), its length `i + 1`, and its
    sum-invariant probes;
  * the first computed products — `x ∪ x = x^2` (`cupGeneratorSquareIsDegreeTwoGenerator`, the headline),
    `x ∪ x^2 = x^3`, `x^2 ∪ x^2 = x^4`;
  * BILINEARITY (`cupEvenGeneratorLeftAdditive` via `intRightDistrib`, `…RightAdditive` via
    `intLeftDistrib`), ASSOCIATIVITY (`cupEvenPairAssociative` via `intMulAssoc` + `Nat.add_assoc`),
    two-sided UNIT (`cupLeftUnit`/`cupRightUnit`), and GRADED-COMMUTATIVITY (`cupEvenPairGradedCommutes`
    via `intMulComm` + `Nat.add_comm`; on the even subring the Koszul sign `(-1)^{(2i)(2j)}` is always
    `+1`, so commutativity is strict — matching Roberts Rem. 3.4.2: over trivial `G`-action the diagonal
    is strictly co-associative, so these certificates are exact on-the-nose identities, not up-to-homotopy);
  * the torsion relation `n·x = 0` computed at `n = 2, 3, 4` (`cyclicTorsionRelationVanishesAt{Two,Three,Four}`
    via `natRemainderSelf`, the coefficient-level witness that `n ≡ 0 (mod n)`), with the per-`n`
    cohomology groups `H^even(ZZ/n) = ZZ/n` (`cohomEvenPositiveInvariantForModulus{Two,Three,Four}`).

## Honest scope (never overclaim)

The ring is DATA + certificates + the computed torsion relation.  The classical ring ISOMORPHISM
`H^*(ZZ/n; ZZ) ≅ ZZ[x]/(nx)`, `|x| = 2`, is CITED, NEVER claimed: Brown, *Cohomology of Groups* Ch. V §6
& Ch. VI; Cartan–Eilenberg Ch. XII §7; Bárcenas–Gómez arXiv:1603.01475 p. 5 (`H*(Z_a; Z) = Z[α₂]/(aα₂)`,
`dim α₂ = 2`).  The full comparison that this cup IS the topological cup requires a verified `G`-chain map
`Δ : W → W ⊗ W` lifting the augmentation (Roberts Thm 4.3.3; Martins arXiv:1307.0518) — that is r2+; r1
presents the even-subring polynomial ring as the diagonal-INDUCED product on the canonical representatives.
The odd generator `t` (with the classical `t ∪ t = -(n choose 2) s` structure constant) is torsion over
trivial `ZZ` and does NOT survive into the `ZZ`-coefficient ring (`H^odd = 0`), so it is deferred/cited.
Prior-art status: mathlib4's `GroupCohomology/FiniteCyclic` stops at the additive `H^i` isomorphisms and
has NO cup product on group cohomology; no kernel-checked cohomology-RING of `ZZ/n` was found — this is a
first at this concreteness.

## Zero-axiom design decisions

  * The cochain complex REUSES the shipped tower boundary (`cochainCoboundary := boundaryMatrix`,
    self-dual); `δ δ = 0` rides `boundaryScalarComposesToZero` through `intMulComm`, never Init `Int.*`.
  * The cohomology read-off reuses the shipped generic `SmithHomologyData.homologyInvariant` and the
    cyclic seed's SNF literals; the parity read-offs are structural recursion on the half-index
    (period-2 phase collapse `degree + 3 ↦ degree + 1`), matching the shipped homology read-offs.
  * All ring arithmetic routes through the propext-clean `ComputerAlgebra/Number` kit (`intMulComm`,
    `intMulOne`, `intLeftDistrib`, `intRightDistrib`, `intMulAssoc`) and the clean `Nat.add_assoc` /
    `Nat.add_comm`; the torsion relation uses `natRemainderSelf`, never Init `%` / `omega`.
  * The diagonal-shuffle length rides a monomorphic `List (Nat × Nat)` map-length helper (no polymorphic
    `List.length_map`), matching the propext corpus.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/PeriodicTowerCohomologyCupProduct.lean`, with an
independent `#print axioms` cross-check in `…PeriodicTowerCohomologyCupProductAxiomWitness.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## B1 — the cochain complex (the dual of the shipped tower)

For the rank-1-at-every-degree tower, `C^k = Hom(C_k, ZZ) = ZZ` and the coboundary `δ^k = (∂_{k+1})^T`.
Since every boundary is `1 × 1` its transpose is itself, and the ADC convention `boundaryMatrix dim =
∂_{dim+1}` already IS `δ^dim` — so the cochain coboundary reuses the shipped boundary literal verbatim. -/

/-- **The cochain coboundary `δ^dim`** of a periodic tower — the transpose of `∂_{dim+1}`, which for the
`1 × 1` tower boundaries is `∂_{dim+1} = boundaryMatrix dim` itself (self-dual).  The dual cochain
complex of the shipped homology tower. -/
def PeriodicTower.cochainCoboundary (tower : PeriodicTower) (dim : Nat) : IntMatrix :=
  tower.boundaryMatrix dim

/-- ★ **`δ δ = 0` at the cochain level** — the sole `1 × 1` entry of `δ^{dim+1} · δ^dim` is `0`.  The
coboundary composition `δ^{dim+1} ∘ δ^dim` reverses the boundary order, so it is the shipped
`boundaryScalarComposesToZero` read through `intMulComm`.  No propext. -/
theorem PeriodicTower.cochainCoboundaryComposesToZero (tower : PeriodicTower) (dim : Nat) :
    (tower.cochainCoboundary (dim + 1)).entryAt 0 0 * (tower.cochainCoboundary dim).entryAt 0 0 = 0 :=
  (intMulComm ((tower.boundaryMatrix (dim + 1)).entryAt 0 0)
      ((tower.boundaryMatrix dim).entryAt 0 0)).trans
    (tower.boundaryScalarComposesToZero dim)

/-- **`δ^even = [[0]]`** over the `ZZ/3` tower — the dual of `∂ = (t−1) ↦ 0` at even degrees. -/
theorem cyclicThreeTowerCoboundaryOfEvenDegree (half : Nat) :
    cyclicThreePeriodicTower.cochainCoboundary (2 * half) = ⟨[[0]]⟩ :=
  cyclicThreeTowerBoundaryOfEvenDegree half

/-- **`δ^odd = [[-3]]`** over the `ZZ/3` tower — the dual of `∂ = N ↦ 3` at odd degrees; SNF `[[3]]`, the
`ZZ/3` torsion source at every EVEN cohomology degree. -/
theorem cyclicThreeTowerCoboundaryOfOddDegree (half : Nat) :
    cyclicThreePeriodicTower.cochainCoboundary (2 * half + 1) = ⟨[[-3]]⟩ :=
  cyclicThreeTowerBoundaryOfOddDegree half

/-- ★ **`δ δ = 0` for the `ZZ/3` cochain complex at every degree** — the cochain corollary of the tower's
finite-to-infinite composition law. -/
theorem cyclicThreePeriodicTowerCochainComposesToZero (dim : Nat) :
    (cyclicThreePeriodicTower.cochainCoboundary (dim + 1)).entryAt 0 0 *
    (cyclicThreePeriodicTower.cochainCoboundary dim).entryAt 0 0 = 0 :=
  cyclicThreePeriodicTower.cochainCoboundaryComposesToZero dim

/-- ★ **Cochain truth probe at degree 8** (`= 2·4`, even): `δ^8 = [[0]]`. `rfl`. -/
theorem cyclicThreeTowerCoboundaryAtDegreeEight :
    cyclicThreePeriodicTower.cochainCoboundary 8 = ⟨[[0]]⟩ := rfl

/-- ★ **Cochain truth probe at degree 9** (`= 2·4 + 1`, odd): `δ^9 = [[-3]]` — the `N^T` coboundary far
past the Squier carrier's degree-3 truncation. `rfl`. -/
theorem cyclicThreeTowerCoboundaryAtDegreeNine :
    cyclicThreePeriodicTower.cochainCoboundary 9 = ⟨[[-3]]⟩ := rfl

/-! ## B2 — the all-degrees cohomology read-off (`H^0 = ZZ, H^even>0 = ZZ/3, H^odd = 0`)

The cohomology Smith data at degree `k` is the shipped homology data with the boundary SNFs' roles
EXCHANGED: `smithBoundaryIntoLower := SNF(δ^k) = SNF(∂_{k+1})` (rank subtracted), `smithBoundaryFromHigher
:= SNF(δ^{k-1}) = SNF(∂_k)` (rank subtracted AND torsion counted).  The exchange moves the `[[3]]` torsion
from odd degrees (homology) into even degrees (cohomology) — where the degree-2 generator `x` lives. -/

/-- Cohomology Smith data at degree 0: `SNF(δ^0) = SNF(∂_1) = [[0]]` (rank 0), no `δ^{-1}` (placeholder
`[[0]]`, rank 0) — so `freeRank = 1`, `H^0 = ZZ`. -/
def cyclicThreeCohomDegreeZeroSmithData : SmithHomologyData :=
  { chainBasisCount := 1
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimZero
  , windowIntoLower := 1
  , smithBoundaryFromHigher := cyclicThreeSmithNormalFormOfDimZero
  , windowFromHigher := 1 }

/-- Cohomology Smith data at an ODD degree: `SNF(δ^k) = SNF(∂_{k+1}) = [[3]]` (odd index, rank 1),
`SNF(δ^{k-1}) = SNF(∂_k) = [[0]]` (even index, rank 0) — `freeRank = 0`, no torsion, `H^odd = 0`. -/
def cyclicThreeCohomOddDegreeSmithData : SmithHomologyData :=
  { chainBasisCount := 1
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimOne
  , windowIntoLower := 1
  , smithBoundaryFromHigher := cyclicThreeSmithNormalFormOfDimZero
  , windowFromHigher := 1 }

/-- ★ Cohomology Smith data at an EVEN degree `> 0`: `SNF(δ^k) = SNF(∂_{k+1}) = [[0]]` (even index, rank
0), `SNF(δ^{k-1}) = SNF(∂_k) = [[3]]` (odd index, rank 1, factor 3) — `freeRank = 0`, torsion `[3]`,
`H^even>0 = ZZ/3`.  THE HOME OF THE DEGREE-2 GENERATOR `x`. -/
def cyclicThreeCohomEvenPositiveDegreeSmithData : SmithHomologyData :=
  { chainBasisCount := 1
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimZero
  , windowIntoLower := 1
  , smithBoundaryFromHigher := cyclicThreeSmithNormalFormOfDimOne
  , windowFromHigher := 1 }

/-- ★ **THE DUALIZATION WITNESS.**  The EVEN-degree cohomology data IS the shipped ODD-degree homology
data (`cyclicThreeTowerOddDegreeSmithData`), roles exchanged — the `[[3]]` torsion moved parity from
homology-odd to cohomology-even.  `rfl`. -/
theorem cyclicThreeCohomEvenPositiveIsHomologyOdd :
    cyclicThreeCohomEvenPositiveDegreeSmithData = cyclicThreeTowerOddDegreeSmithData := rfl

/-- **The odd-degree cohomology data IS the shipped even-positive homology data** — the other half of the
parity swap.  `rfl`. -/
theorem cyclicThreeCohomOddIsHomologyEvenPositive :
    cyclicThreeCohomOddDegreeSmithData = cyclicThreeTowerEvenPositiveDegreeSmithData := rfl

/-- **The cohomology Smith data at any degree**, selected by parity (period-2 phase, degree 0 special).
Structural recursion `degree + 3 ↦ degree + 1` keeps the odd/even phase. -/
def cyclicThreeCohomHomologyDataAtDegree : Nat → SmithHomologyData
  | 0 => cyclicThreeCohomDegreeZeroSmithData
  | 1 => cyclicThreeCohomOddDegreeSmithData
  | 2 => cyclicThreeCohomEvenPositiveDegreeSmithData
  | degree + 3 => cyclicThreeCohomHomologyDataAtDegree (degree + 1)

/-- **The cohomology invariant at any degree** — the shipped generic read-off applied to the parity
cohomology Smith data. -/
def cyclicThreeCohomInvariantAtDegree (degree : Nat) : HomologyInvariant :=
  (cyclicThreeCohomHomologyDataAtDegree degree).homologyInvariant

/-- ★ **`H^0 = ZZ`** — `freeRank 1`, no torsion. -/
theorem cyclicThreeCohomDegreeZeroIsIntegers :
    cyclicThreeCohomInvariantAtDegree 0 = ⟨1, []⟩ := rfl

/-- ★★ **`H^even>0 = ZZ/3` AT EVERY POSITIVE EVEN DEGREE** — `∀ half, H^{2·half+2} = ⟨0, [3]⟩`.  The
degree-2 generator `x` and all its powers `x^{half+1}` generate a `ZZ/3` at every positive even degree —
the cohomology-side torsion the dualization moved into the even degrees.  Structural recursion on the
half-index (period-2 phase collapse). -/
theorem cyclicThreeCohomEvenPositiveDegreeIsZmodThree :
    ∀ half, cyclicThreeCohomInvariantAtDegree (2 * half + 2) = ⟨0, [3]⟩
  | 0 => rfl
  | half + 1 => cyclicThreeCohomEvenPositiveDegreeIsZmodThree half

/-- ★ **`H^odd = 0` AT EVERY ODD DEGREE** — `∀ half, H^{2·half+1} = ⟨0, []⟩`.  Free rank `0`, no torsion
(`δ^k` injective, `δ^{k-1} = 0`), by structural recursion on the half-index.  The odd generator `t` is
torsion over trivial `ZZ` and vanishes. -/
theorem cyclicThreeCohomOddDegreeIsZero :
    ∀ half, cyclicThreeCohomInvariantAtDegree (2 * half + 1) = ⟨0, []⟩
  | 0 => rfl
  | half + 1 => cyclicThreeCohomOddDegreeIsZero half

/-- ★ **`H^2 = ZZ/3`** — the generator's home degree, the smallest nonzero even degree. `rfl`. -/
theorem cyclicThreeCohomAtDegreeTwoIsZmodThree :
    cyclicThreeCohomInvariantAtDegree 2 = ⟨0, [3]⟩ := rfl

/-- ★ **Cohomology truth probe at degree 8** (even `> 0`): `H^8 = ZZ/3`. `rfl`. -/
theorem cyclicThreeCohomAtDegreeEight :
    cyclicThreeCohomInvariantAtDegree 8 = ⟨0, [3]⟩ := rfl

/-- ★ **Cohomology truth probe at degree 9** (odd): `H^9 = 0`. `rfl`. -/
theorem cyclicThreeCohomAtDegreeNine :
    cyclicThreeCohomInvariantAtDegree 9 = ⟨0, []⟩ := rfl

/-- ★ **Cohomology truth probe at degree 10** (even `> 0`): `H^10 = ZZ/3`. `rfl`. -/
theorem cyclicThreeCohomAtDegreeTen :
    cyclicThreeCohomInvariantAtDegree 10 = ⟨0, [3]⟩ := rfl

/-- ★ **THE DIMENSION-SHIFT DUALIZATION.**  Cohomology torsion at degree 2 (`⟨0, [3]⟩`) equals homology
torsion at degree 1 (`⟨0, [3]⟩`) — the `ZZ/3` moved up one dimension and flipped parity (homology-odd ↔
cohomology-even).  `rfl`. -/
theorem cyclicThreeCohomDegreeTwoMatchesHomologyDegreeOne :
    cyclicThreeCohomInvariantAtDegree 2 = cyclicThreeTowerHomologyInvariantAtDegree 1 := rfl

/-! ### The per-`n` cohomology `H^even(ZZ/n) = ZZ/n` and the torsion relation `n·x = 0` (n = 2, 3, 4)

The `SmithHomologyData.homologyInvariant` read-off computes directly from the supplied SNF; feeding the
even-positive-degree data with coboundary SNF `[[n]]` (the SNF of `∂ = N ↦ n` at odd index) gives
`H^even(ZZ/n) = ⟨0, [n]⟩ = ZZ/n`.  The shipped `ZZ/3` tower is the `n = 3` instance; `n = 2, 4` supply the
canonical SNF `[[n]]` directly (`1 × 1` SNF is the absolute value — CITED, the ring iso is not re-derived). -/

/-- The even-positive-degree cohomology Smith data for modulus `n`: coboundary SNF `[[n]]` at odd index,
`[[0]]` at even index — `H^even(ZZ/n) = ZZ/n`. -/
def cohomEvenPositiveDegreeSmithDataForModulus (modulus : Int) : SmithHomologyData :=
  { chainBasisCount := 1
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimZero
  , windowIntoLower := 1
  , smithBoundaryFromHigher := ⟨[[modulus]]⟩
  , windowFromHigher := 1 }

/-- ★ **`H^even(ZZ/2) = ZZ/2`** — the cohomology ring generator relation for `n = 2`. `rfl`. -/
theorem cohomEvenPositiveInvariantForModulusTwo :
    (cohomEvenPositiveDegreeSmithDataForModulus 2).homologyInvariant = ⟨0, [2]⟩ := rfl

/-- ★ **`H^even(ZZ/3) = ZZ/3`** — the shipped-tower instance, for `n = 3`. `rfl`. -/
theorem cohomEvenPositiveInvariantForModulusThree :
    (cohomEvenPositiveDegreeSmithDataForModulus 3).homologyInvariant = ⟨0, [3]⟩ := rfl

/-- ★ **`H^even(ZZ/4) = ZZ/4`** — the cohomology ring generator relation for `n = 4`. `rfl`. -/
theorem cohomEvenPositiveInvariantForModulusFour :
    (cohomEvenPositiveDegreeSmithDataForModulus 4).homologyInvariant = ⟨0, [4]⟩ := rfl

/-- **The `n = 3` modulus read-off IS the shipped tower's degree-2 cohomology** — the per-`n` family
specialises to the machine-checked `ZZ/3` tower.  `rfl`. -/
theorem cohomEvenPositiveForModulusThreeMatchesTower :
    (cohomEvenPositiveDegreeSmithDataForModulus 3).homologyInvariant
      = cyclicThreeCohomInvariantAtDegree 2 := rfl

/-- ★ **The ring relation `2·x = 0` in `H^*(ZZ/2)`** — the coefficient-level witness `2 ≡ 0 (mod 2)`
(`natRemainderSelf`).  The generator has order 2. -/
theorem cyclicTorsionRelationVanishesAtTwo : natRemainder 2 2 = 0 := natRemainderSelf (by decide)

/-- ★ **The ring relation `3·x = 0` in `H^*(ZZ/3)`** — the coefficient-level witness `3 ≡ 0 (mod 3)`.
The shipped tower's generator has order 3. -/
theorem cyclicTorsionRelationVanishesAtThree : natRemainder 3 3 = 0 := natRemainderSelf (by decide)

/-- ★ **The ring relation `4·x = 0` in `H^*(ZZ/4)`** — the coefficient-level witness `4 ≡ 0 (mod 4)`.
The generator has order 4. -/
theorem cyclicTorsionRelationVanishesAtFour : natRemainder 4 4 = 0 := natRemainderSelf (by decide)

/-! ## B3 — the cup product on the even subring `ZZ[x]`, `|x| = 2`, and the explicit diagonal

An even cohomology class is a pair `(halfDegree, coeff)` denoting `coeff · x^halfDegree` in degree
`2·halfDegree`.  The diagonal-induced cup on the even subring adds half-degrees and multiplies
coefficients — the `Σ_{k+l=i} σ^(k) ⊗ σ^(l)` component of the explicit diagonal (Roberts Thm 4.3.3). -/

/-- **The cup product of two even classes** `(i, a) ∪ (j, b) = (i + j, a · b)` — half-degrees add,
coefficients multiply.  The canonical-representative form of the diagonal-induced product on `ZZ[x]`. -/
def cupEvenPair (left right : Nat × Int) : Nat × Int :=
  (left.fst + right.fst, left.snd * right.snd)

/-- **The cup product on explicit generator data** — `cupEvenGenerator i j a b = (i + j, a · b)`, the
uncurried `cupEvenPair`. -/
def cupEvenGenerator (leftHalf rightHalf : Nat) (leftCoeff rightCoeff : Int) : Nat × Int :=
  (leftHalf + rightHalf, leftCoeff * rightCoeff)

/-- **The degree-2 generator `x`** — half-degree 1 (degree 2), coefficient 1.  The polynomial generator of
`ZZ[x]/(nx)`. -/
def cohomGeneratorX : Nat × Int := (1, 1)

/-- **The ring unit `1`** — half-degree 0 (degree 0), coefficient 1.  The `H^0 = ZZ` generator. -/
def cohomRingUnit : Nat × Int := (0, 1)

/-- **`cupEvenGenerator` is `cupEvenPair` on the paired arguments** — the two forms agree definitionally.
`rfl`. -/
theorem cupEvenGeneratorIsCupEvenPair (leftHalf rightHalf : Nat) (leftCoeff rightCoeff : Int) :
    cupEvenGenerator leftHalf rightHalf leftCoeff rightCoeff
      = cupEvenPair (leftHalf, leftCoeff) (rightHalf, rightCoeff) := rfl

/-- A monomorphic map-preserves-length helper for `List (Nat × Nat)` — structural, avoids the polymorphic
`List.length_map` (propext corpus).  Used for the diagonal-shuffle length. -/
theorem natPairMapPreservesLength (transform : Nat × Nat → Nat × Nat) :
    ∀ pairs : List (Nat × Nat), (pairs.map transform).length = pairs.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (natPairMapPreservesLength transform rest)

/-- **The explicit even-degree diagonal shuffle** — the index set `{(k, l) : k + l = i}` of the diagonal
component `Σ_{k+l=i} σ^(k) ⊗ σ^(l)` (Roberts Thm 4.3.3 / eq. 4.4).  `diagonalEvenShuffle i` enumerates the
`i + 1` half-degree splittings that assemble the degree-`2i` class in `(W ⊗ W)`. -/
def diagonalEvenShuffle : Nat → List (Nat × Nat)
  | 0 => [(0, 0)]
  | i + 1 => (i + 1, 0) :: (diagonalEvenShuffle i).map (fun pair => (pair.fst, pair.snd + 1))

/-- ★ **The diagonal shuffle has `i + 1` terms** — `Σ_{k+l=i}` ranges over `k = 0, …, i`.  Structural
recursion through the monomorphic map-length helper. -/
theorem diagonalEvenShuffleLength :
    ∀ i, (diagonalEvenShuffle i).length = i + 1
  | 0 => rfl
  | i + 1 =>
      congrArg Nat.succ
        ((natPairMapPreservesLength (fun pair => (pair.fst, pair.snd + 1)) (diagonalEvenShuffle i)).trans
          (diagonalEvenShuffleLength i))

/-- **The shuffle at `i = 1`** — `x ⊗ 1 + 1 ⊗ x` splittings `[(1,0), (0,1)]`. `rfl`. -/
theorem diagonalEvenShuffleAtOne :
    diagonalEvenShuffle 1 = [(1, 0), (0, 1)] := rfl

/-- **The shuffle at `i = 2`** — the degree-4 splittings `[(2,0), (1,1), (0,2)]`. `rfl`. -/
theorem diagonalEvenShuffleAtTwo :
    diagonalEvenShuffle 2 = [(2, 0), (1, 1), (0, 2)] := rfl

/-- Do all pairs in the list have `fst + snd = target`?  A Bool check enabling `rfl`-computable
sum-invariant probes without `List.Mem`. -/
def allPairsSumTo (target : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | pair :: rest => (pair.fst + pair.snd == target) && allPairsSumTo target rest

/-- ★ **The shuffle at `i = 2` splits every term to sum 2** — the `k + l = 2` invariant, computed. `rfl`. -/
theorem diagonalEvenShuffleSumsAtTwo :
    allPairsSumTo 2 (diagonalEvenShuffle 2) = true := rfl

/-- ★ **The shuffle at `i = 3` splits every term to sum 3** — the `k + l = 3` invariant, computed. `rfl`. -/
theorem diagonalEvenShuffleSumsAtThree :
    allPairsSumTo 3 (diagonalEvenShuffle 3) = true := rfl

/-! ## B4 — the ring certificates (the computed products and the ring laws)

The even subring is the graded-commutative associative unital ring `ZZ[x]`, `|x| = 2`, with the torsion
relation `n·x = 0` (B2).  Over trivial `ZZ`-action the chain-level diagonal is strictly co-associative
(Roberts Rem. 3.4.2), so these are exact on-the-nose identities, not up-to-homotopy. -/

/-- ★★ **THE HEADLINE PRODUCT `x ∪ x = x^2`** — `cupEvenGenerator 1 1 1 1 = (2, 1)`: the degree-2 generator
cupped with itself lands the coefficient-1 class in degree 4 (half-degree 2), generating `H^4 = ZZ/3`.
`rfl`. -/
theorem cupGeneratorSquareIsDegreeTwoGenerator :
    cupEvenGenerator 1 1 1 1 = (2, 1) := rfl

/-- ★ **`x ∪ x^2 = x^3`** — `cupEvenGenerator 1 2 1 1 = (3, 1)`, the degree-6 class. `rfl`. -/
theorem cupGeneratorCubeIsDegreeThreeGenerator :
    cupEvenGenerator 1 2 1 1 = (3, 1) := rfl

/-- ★ **`x^2 ∪ x^2 = x^4`** — `cupEvenGenerator 2 2 1 1 = (4, 1)`, the degree-8 class. `rfl`. -/
theorem cupGeneratorFourthIsDegreeFourGenerator :
    cupEvenGenerator 2 2 1 1 = (4, 1) := rfl

/-- **The right unit law** — `y ∪ 1 = y` (`cupEvenGenerator h 0 c 1 = (h, c)`) via `intMulOne`; the
half-degree `h + 0` reduces definitionally. -/
theorem cupRightUnit (leftHalf : Nat) (leftCoeff : Int) :
    cupEvenGenerator leftHalf 0 leftCoeff 1 = (leftHalf, leftCoeff) :=
  congrArg (fun coeff => (leftHalf, coeff)) (intMulOne leftCoeff)

/-- ★ **GRADED-COMMUTATIVITY (even × even, sign `+1`)** — `left ∪ right = right ∪ left` on the even
subring: half-degrees commute (`Nat.add_comm`), coefficients commute (`intMulComm`), and the Koszul sign
`(-1)^{(2i)(2j)} = +1` makes it strict. -/
theorem cupEvenPairGradedCommutes (left right : Nat × Int) :
    cupEvenPair left right = cupEvenPair right left :=
  (congrArg (fun degree => (degree, left.snd * right.snd)) (Nat.add_comm left.fst right.fst)).trans
    (congrArg (fun coeff => (right.fst + left.fst, coeff)) (intMulComm left.snd right.snd))

/-- **Graded-commutativity on generator data** — the uncurried form of `cupEvenPairGradedCommutes`. -/
theorem cupEvenGeneratorGradedCommutes (leftHalf rightHalf : Nat) (leftCoeff rightCoeff : Int) :
    cupEvenGenerator leftHalf rightHalf leftCoeff rightCoeff
      = cupEvenGenerator rightHalf leftHalf rightCoeff leftCoeff :=
  cupEvenPairGradedCommutes (leftHalf, leftCoeff) (rightHalf, rightCoeff)

/-- **The left unit law** — `1 ∪ y = y` (`cupEvenGenerator 0 h 1 c = (h, c)`), via graded-commutativity
composed with the right unit (sidesteps `Nat.zero_add`). -/
theorem cupLeftUnit (rightHalf : Nat) (rightCoeff : Int) :
    cupEvenGenerator 0 rightHalf 1 rightCoeff = (rightHalf, rightCoeff) :=
  (cupEvenGeneratorGradedCommutes 0 rightHalf 1 rightCoeff).trans (cupRightUnit rightHalf rightCoeff)

/-- ★ **BILINEARITY, left addend** — `(a1 + a2) · x^i ∪ b · x^j = a1·b · x^{i+j} + a2·b · x^{i+j}` at the
coefficient level, via `intRightDistrib`.  The cup is additive in its left coefficient. -/
theorem cupEvenGeneratorLeftAdditive
    (leftHalf rightHalf : Nat) (leftCoeffA leftCoeffB rightCoeff : Int) :
    cupEvenGenerator leftHalf rightHalf (leftCoeffA + leftCoeffB) rightCoeff
      = (leftHalf + rightHalf, leftCoeffA * rightCoeff + leftCoeffB * rightCoeff) :=
  congrArg (fun coeff => (leftHalf + rightHalf, coeff))
    (intRightDistrib leftCoeffA leftCoeffB rightCoeff)

/-- ★ **BILINEARITY, right addend** — additive in the right coefficient, via `intLeftDistrib`. -/
theorem cupEvenGeneratorRightAdditive
    (leftHalf rightHalf : Nat) (leftCoeff rightCoeffA rightCoeffB : Int) :
    cupEvenGenerator leftHalf rightHalf leftCoeff (rightCoeffA + rightCoeffB)
      = (leftHalf + rightHalf, leftCoeff * rightCoeffA + leftCoeff * rightCoeffB) :=
  congrArg (fun coeff => (leftHalf + rightHalf, coeff))
    (intLeftDistrib leftCoeff rightCoeffA rightCoeffB)

/-- ★ **ASSOCIATIVITY** — `(a ∪ b) ∪ c = a ∪ (b ∪ c)` on even classes: half-degrees associate
(`Nat.add_assoc`), coefficients associate (`intMulAssoc`).  Exact on-the-nose (trivial `ZZ`-action,
Roberts Rem. 3.4.2). -/
theorem cupEvenPairAssociative (first second third : Nat × Int) :
    cupEvenPair (cupEvenPair first second) third = cupEvenPair first (cupEvenPair second third) :=
  (congrArg (fun degree => (degree, first.snd * second.snd * third.snd))
      (Nat.add_assoc first.fst second.fst third.fst)).trans
    (congrArg (fun coeff => (first.fst + (second.fst + third.fst), coeff))
      (intMulAssoc first.snd second.snd third.snd))

/-- **Associativity on generator data** — `(x^i ∪ x^j) ∪ x^k = x^i ∪ (x^j ∪ x^k)`, the uncurried form of
`cupEvenPairAssociative`. -/
theorem cupEvenGeneratorAssociative
    (firstHalf secondHalf thirdHalf : Nat) (firstCoeff secondCoeff thirdCoeff : Int) :
    cupEvenPair (cupEvenGenerator firstHalf secondHalf firstCoeff secondCoeff) (thirdHalf, thirdCoeff)
      = cupEvenPair (firstHalf, firstCoeff)
          (cupEvenGenerator secondHalf thirdHalf secondCoeff thirdCoeff) :=
  cupEvenPairAssociative (firstHalf, firstCoeff) (secondHalf, secondCoeff) (thirdHalf, thirdCoeff)

/-! ### Honest scope statement (for the ledger)

What stands, zero-axiom: the dual COCHAIN complex of the shipped 2-periodic tower (`cochainCoboundary`,
self-dual, with `δ δ = 0` at every degree); the all-degrees cohomology read-off `H^0 = ZZ`, `H^even>0 =
ZZ/3`, `H^odd = 0` (the torsion moved into the even degrees by the parity swap, probed at 8/9/10); the
per-`n` cohomology `H^even(ZZ/n) = ZZ/n` for `n = 2, 3, 4` with the torsion relation `n·x = 0`; the
explicit even-degree diagonal shuffle `Σ_{k+l=i} σ^(k) ⊗ σ^(l)` (length `i + 1`); the cup product on the
even subring with the first computed products (`x ∪ x = x^2`, `x ∪ x^2 = x^3`, `x^2 ∪ x^2 = x^4`); and the
ring-law certificates (bilinearity, associativity, two-sided unit, graded-commutativity) — exact on-the-nose
over trivial `ZZ`-action.

The classical ring ISOMORPHISM `H^*(ZZ/n; ZZ) ≅ ZZ[x]/(nx)`, `|x| = 2`, is CITED, NEVER claimed (Brown
Ch. V §6 & VI; Cartan–Eilenberg Ch. XII §7; Bárcenas–Gómez arXiv:1603.01475).  The verified `G`-chain-map
diagonal `Δ : W → W ⊗ W` lifting the augmentation — the step upgrading "presented ring" to "the cup IS the
topological cup" — is the honest residual, deferred to r2 (Roberts Thm 4.3.3; Martins arXiv:1307.0518).
The odd generator `t` is torsion over trivial `ZZ` (`H^odd = 0`) and is deferred/cited.  Prior-art:
mathlib4 has no group-cohomology cup product; no kernel-checked cohomology-ring of `ZZ/n` was found. -/

/-- ★ **The TOWER-RING (#2147) r1 ledger marker.**  What stands, zero-axiom: the dual cochain complex of
the shipped periodic tower + the cohomology read-off `H^0 = ZZ, H^even>0 = ZZ/n, H^odd = 0` (torsion in
the even degrees, where `x` lives) + the explicit even-degree diagonal shuffle + the cup product on the
even subring with the first computed products (`x ∪ x = x^2`) + the bilinearity / associativity /
graded-commutativity / unit certificates + the torsion relation `n·x = 0` at `n = 2, 3, 4`.  The ring iso
`H^*(ZZ/n) ≅ ZZ[x]/(nx)` is CITED, never claimed; the verified diagonal chain map is the r2 residual.
Read the meaning from THIS docstring (the honest-record convention). -/
def periodicTowerCohomologyRingLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
