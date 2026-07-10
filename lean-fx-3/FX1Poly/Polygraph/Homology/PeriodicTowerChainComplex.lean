import FX1Poly.Polygraph.Homology.PolygraphHomologyFinitenessInvariant
import FX1Poly.ComputerAlgebra.Number.NatModularReduction
import FX1Poly.ComputerAlgebra.Number.IntArithmeticCore

/-! # FX1Poly/Polygraph/Homology/PeriodicTowerChainComplex — the 2-PERIODIC group-homology tower of
    `ZZ/3`, a NON-TRUNCATED augmented directed complex from ONE loop of boundary data, with the
    finite-check-to-infinite-conclusion `d d = 0` and the all-degrees homology read-off
    `H0 = ZZ, H_odd = ZZ/3, H_even>0 = 0` (TOWER-PERIODIC, #2146)

The shipped `Homology/CyclicThreeChainComplex` computes the SQUIER (polygraphic) chain complex of the
walker `⟨s | sss ⟹ id⟩` — a complex TRUNCATED at degree 3 (critical PAIRS only, `basisCount ≥ 4 = 0`).
This module ships the COMPLEMENTARY object: the standard 2-PERIODIC group-homology free resolution of
`ZZ/3` (Brown, *Cohomology of Groups*, Ch. I §6 & Ch. VI), tensored down to trivial `ZZ` coefficients.
Both resolve `ZZ` over `ZZ[ZZ/3]`, so they are chain-homotopy equivalent and share `H_*` (fundamental
lemma of homological algebra), but as CHAIN COMPLEXES they differ — the periodic one is minimal, has a
NONZERO basis atom at EVERY degree, and never truncates.

## The math (compute first, state after)

`ZZ/3 = ⟨t | t³ = 1⟩` has the 2-periodic free resolution over `ZZ[ZZ/3]`:

  `⋯ → ZZ[G] --(t−1)--> ZZ[G] --N--> ZZ[G] --(t−1)--> ZZ[G] --eps--> ZZ → 0`,   `N = 1 + t + t²`.

Tensoring `ZZ ⊗ −` (`t ↦ 1`) sends `(t−1) ↦ 0` and `N ↦ 3`, and every chain group becomes `ZZ` (rank 1
at EVERY degree).  In the ADC convention `boundaryMatrix dim = d_{dim+1}`, so:

  `boundaryMatrix (even dim) = [[0]]`   (`∂_odd-index = (t−1) ↦ 0`),
  `boundaryMatrix (odd dim)  = [[-3]]`  (`∂_even-index = N ↦ 3`; sign `[[-3]]` reuses the cyclic seed).

The loop of boundary DATA is `[ [[0]] , [[-3]] ]`, period `2`.  The ONE loop check (both residues,
wraparound included) is degenerate-by-zero-factor — `loop[0]·loop[1] = 0·(−3) = 0` and
`loop[1]·loop[0] = (−3)·0 = 0` — the honest note of the cyclic/involution seeds, now tower-wide.

Homology (`H_k = ker ∂_k / im ∂_{k+1}`, all SNF windows `1 × 1`):

  | k        | SNF ∂_k | rank ∂_k | SNF ∂_{k+1} | rank | freeRank | torsion | `H_k` |
  |----------|---------|----------|-------------|------|----------|---------|-------|
  | 0        | —       | —        | `[[0]]`     | 0    | 1        | []      | `ZZ`  |
  | odd      | `[[0]]` | 0        | `[[3]]`     | 1    | 0        | [3]     | `ZZ/3`|
  | even > 0 | `[[3]]` | 1        | `[[0]]`     | 0    | 0        | []      | `0`   |

→ `H0 = ZZ, H_odd = ZZ/3, H_{even>0} = 0`.  `H1 = ⟨0,[3]⟩` is defeq the shipped
`cyclicThreeDegreeOneHomologyInvariant`; the odd-degree Smith data IS the shipped
`cyclicThreeDegreeOneSmithData` (`rfl`).

## What is genuinely new (honestly scoped)

The single research increment is the NON-TRUNCATED ADC produced data-drivenly from ONE loop: a
`Nat`-total `basisCount = fun _ => 1` nonzero at EVERY degree, whose `d d = 0` at ALL infinitely many
degrees follows from the `period`-many loop compositions by the modular successor law
`natRemainder (dim+1) period = natRemainder (natRemainder dim period + 1) period`.  This escapes the
`SquierNoGoInterface` DEGREE-TRUNCATION ceiling (`carrierDegreeThreeChainIsAlwaysFinite`: the List
carrier has `basisCount 3 = criticalPairs.length` and nothing above), so the GRADED homology
`⊕_{k} H_k = ZZ ⊕ (⊕_{k odd} ZZ/3)` has infinitely many torsion summands — NOT finitely generated as an
abelian group.  DOUBLE CAVEAT (no overclaim): the tower escapes truncation, NOT per-degree rank
finiteness — each `H_k` is still f.g. (`C_k = ZZ^1`).  Squier's `S_1` needs infinite RANK at ONE degree
(`basisCount → ∞`), which no `Nat`-valued `basisCount` expresses, so this does NOT witness `S_1`; the
no-go's obligation-3 wall stays walled.  The chain-homotopy equivalence to the Squier complex is NOT
formalised (the honest residual).

## Zero-axiom design decisions

  * The carrier is the shipped `AugmentedDirectedComplex`; `PeriodicTower` is a PRODUCER of one, not a
    replacement — every match stays on non-indexed inductives.
  * Boundary indexing is the propext-clean `natRemainder` (`NatModularReduction`), never Init `%`; the
    residue parity/successor lemmas ride `natRemainderUnique` / `natRemainderAddPush` /
    `natRemainderAddMultiple`.
  * `d d = 0` routes through `intZeroMul` / `intMulZero` / `intZeroAdd` (`IntArithmeticCore`), never the
    propext-dirty Init `Int.zero_mul` / `Int.mul_zero` / `Int.zero_add`.
  * The homology read-off reuses the shipped generic `SmithHomologyData.homologyInvariant` and the
    cyclic seed's SNF literals / reduction certificates verbatim.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/PeriodicTowerChainComplex.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the carrier: `PeriodicTower`, its boundary function, and the periodicity certificate -/

/-- **A periodic tower of boundary data.**  ONE loop `loopBoundaries` of `1 × 1` integer matrices — one
per residue class mod `period` — extended to ALL degrees by index-mod-`period`.  `firstBoundaryVanishes`
is the augmentation-compatibility condition `eps ∘ ∂₁ = 0` (`∂₁` maps into the augmentation ideal, so
the residue-0 boundary's sole entry is `0`); `loopComposesToZero` is the ONE finite check (the
`period`-many consecutive loop compositions, cyclic successor included) from which `d d = 0` at every
degree follows.  A PRODUCER of `AugmentedDirectedComplex` with `basisCount = fun _ => 1` — the first
non-degree-truncated ADC in the lane. -/
structure PeriodicTower where
  /-- The loop of boundary literals, one `1 × 1` matrix per residue class. -/
  loopBoundaries : List IntMatrix
  /-- The period — the number of residue classes. -/
  period : Nat
  /-- The period is positive (so `natRemainder _ period` is bounded and residue-0 is reachable). -/
  periodPositive : 0 < period
  /-- The loop has exactly `period` entries (well-formedness: period = number of residues). -/
  loopMatchesLength : loopBoundaries.length = period
  /-- Every in-range loop boundary is the `1 × 1` shape (so every tower boundary is `1 × 1`). -/
  loopRectangular : ∀ i, i < period →
    (listGetWithDefault (⟨[]⟩ : IntMatrix) loopBoundaries i).IsRectangular 1 1
  /-- The residue-0 boundary's sole entry vanishes — the augmentation-compatibility `eps ∘ ∂₁ = 0`. -/
  firstBoundaryVanishes :
    (listGetWithDefault (⟨[]⟩ : IntMatrix) loopBoundaries 0).entryAt 0 0 = 0
  /-- ★ **THE ONE FINITE CHECK.**  Each residue's boundary composes with its cyclic successor's to `0` —
  the `period`-many consecutive compositions, wraparound included. -/
  loopComposesToZero : ∀ i, i < period →
    (listGetWithDefault (⟨[]⟩ : IntMatrix) loopBoundaries i).entryAt 0 0 *
    (listGetWithDefault (⟨[]⟩ : IntMatrix) loopBoundaries (natRemainder (i + 1) period)).entryAt 0 0 = 0

/-- The tower's boundary at degree `dim` — the loop boundary at residue `dim mod period`.  Total,
nonzero-shaped at EVERY degree (the non-truncation). -/
def PeriodicTower.boundaryMatrix (tower : PeriodicTower) (dim : Nat) : IntMatrix :=
  listGetWithDefault ⟨[]⟩ tower.loopBoundaries (natRemainder dim tower.period)

/-- ★ **THE PERIODICITY CERTIFICATE.**  `boundaryMatrix (dim + period) = boundaryMatrix dim` — forced by
the mod-indexed construction, discharged by the single residue-invariance lemma
`natRemainderAddMultiple` (adding one multiple of `period` leaves the residue unchanged).  No propext. -/
theorem PeriodicTower.boundaryPeriodicity (tower : PeriodicTower) (dim : Nat) :
    tower.boundaryMatrix (dim + tower.period) = tower.boundaryMatrix dim :=
  let residueStep : natRemainder (dim + tower.period * 1) tower.period = natRemainder dim tower.period :=
    natRemainderAddMultiple dim tower.period 1 tower.periodPositive
  let collapseMultiple : dim + tower.period * 1 = dim + tower.period :=
    congrArg (dim + ·) (Nat.mul_one tower.period)
  let residuePeriodicity : natRemainder (dim + tower.period) tower.period = natRemainder dim tower.period :=
    collapseMultiple ▸ residueStep
  congrArg (listGetWithDefault (⟨[]⟩ : IntMatrix) tower.loopBoundaries) residuePeriodicity

/-- Every tower boundary matrix has the declared `1 × 1` shape — from `loopRectangular` at the bounded
residue.  The `boundaryHasDimensions` obligation of the produced ADC. -/
theorem PeriodicTower.boundaryRectangular (tower : PeriodicTower) (dim : Nat) :
    (tower.boundaryMatrix dim).IsRectangular 1 1 :=
  tower.loopRectangular (natRemainder dim tower.period)
    (natRemainderIsBounded tower.periodPositive)

/-! ## B2 — the finite-check-to-infinite-conclusion `d d = 0`

The `period`-many loop compositions (`loopComposesToZero`, the FINITE input) lift to `d d = 0` at ALL
degrees: at degree `dim` the composition is the loop check at residue `natRemainder dim period`, with the
next boundary's residue matched by the modular successor law `natRemainderAddPush`. -/

/-- ★ **The scalar `d d = 0` at any degree** — the sole `1 × 1` entry of `boundaryMatrix dim ·
boundaryMatrix (dim+1)` is `0`.  The loop check at residue `natRemainder dim period` composes the
residue's boundary with its cyclic successor's; `natRemainderAddPush` identifies that successor residue
with `natRemainder (dim+1) period`.  THE finite-to-infinite step. -/
theorem PeriodicTower.boundaryScalarComposesToZero (tower : PeriodicTower) (dim : Nat) :
    (tower.boundaryMatrix dim).entryAt 0 0 * (tower.boundaryMatrix (dim + 1)).entryAt 0 0 = 0 := by
  have loopZero := tower.loopComposesToZero (natRemainder dim tower.period)
    (natRemainderIsBounded tower.periodPositive)
  have successorResidue :
      natRemainder (natRemainder dim tower.period + 1) tower.period
        = natRemainder (dim + 1) tower.period :=
    natRemainderAddPush dim 1 tower.period tower.periodPositive
  rw [successorResidue] at loopZero
  exact loopZero

/-- **`d d = 0` in the ADC window shape** (`row, col < 1`) — the scalar step wrapped in the length-1
finite sum; out-of-window row/col refuted by the propext-clean peel.  Feeds the ADC
`boundaryComposesToZero` field. -/
theorem PeriodicTower.boundaryComposesToZero (tower : PeriodicTower) :
    ∀ (dim rowIndex colIndex : Nat), rowIndex < 1 → colIndex < 1 →
      sumOverIndices 1 (fun middleIndex =>
        (tower.boundaryMatrix dim).entryAt rowIndex middleIndex *
        (tower.boundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0
  | dim, 0, 0, _, _ =>
      (intZeroAdd _).trans (tower.boundaryScalarComposesToZero dim)
  | _, 0, _ + 1, _, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc colBound))
  | _, _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))

/-- **`eps ∘ d0 = 0`** — the augmentation `[1]` kills the residue-0 boundary via `firstBoundaryVanishes`.
Feeds the ADC `augmentationComposesToZero` field. -/
theorem PeriodicTower.augmentationComposesToZero (tower : PeriodicTower) :
    ∀ (colIndex : Nat), colIndex < 1 →
      sumOverIndices 1 (fun middleIndex =>
        listGetWithDefault (0 : Int) [1] middleIndex *
        (tower.boundaryMatrix 0).entryAt middleIndex colIndex) = 0
  | 0, _ => by
      have firstEntryZero : (tower.boundaryMatrix 0).entryAt 0 0 = 0 :=
        (congrArg (fun boundary => boundary.entryAt 0 0)
          (congrArg (listGetWithDefault (⟨[]⟩ : IntMatrix) tower.loopBoundaries)
            (natRemainderOfLt tower.periodPositive))).trans tower.firstBoundaryVanishes
      show (0 : Int) + 1 * (tower.boundaryMatrix 0).entryAt 0 0 = 0
      rw [firstEntryZero]
      exact (intZeroAdd _).trans (intMulZero 1)
  | _ + 1, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc colBound))

/-- **The produced augmented directed complex.**  `basisCount = fun _ => 1` (rank 1, nonzero at EVERY
degree — the non-truncation), boundary by mod-indexing, augmentation `[1]`; all four obligations
discharged from the loop data. -/
def PeriodicTower.toAugmentedDirectedComplex (tower : PeriodicTower) : AugmentedDirectedComplex where
  basisCount := fun _ => 1
  boundaryMatrix := tower.boundaryMatrix
  augmentation := [1]
  boundaryHasDimensions := fun dim => tower.boundaryRectangular dim
  augmentationHasWidth := rfl
  boundaryComposesToZero := tower.boundaryComposesToZero
  augmentationComposesToZero := tower.augmentationComposesToZero

/-- ★ **`d d = 0` as a FIELD of the shipped ADC** — the tower's chain obligation read back off the
produced `AugmentedDirectedComplex`.  Confirms the producer lands a genuine augmented directed complex. -/
theorem PeriodicTower.chainComplexBoundaryComposesToZero (tower : PeriodicTower)
    (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < tower.toAugmentedDirectedComplex.basisCount dim)
    (colBound : colIndex < tower.toAugmentedDirectedComplex.basisCount (dim + 2)) :
    sumOverIndices (tower.toAugmentedDirectedComplex.basisCount (dim + 1)) (fun middleIndex =>
      (tower.toAugmentedDirectedComplex.boundaryMatrix dim).entryAt rowIndex middleIndex *
      (tower.toAugmentedDirectedComplex.boundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  tower.toAugmentedDirectedComplex.boundaryComposesToZero dim rowIndex colIndex rowBound colBound

/-! ## B1/B2 — the `ZZ/3` instance: the loop data, the ONE loop check, the tower -/

/-- The `ZZ/3` loop of boundary data: `∂₁ = (t−1) ↦ [[0]]` at residue 0, `∂₂ = N ↦ [[-3]]` at residue 1.
Period 2. -/
def cyclicThreePeriodicLoopBoundaries : List IntMatrix := [⟨[[0]]⟩, ⟨[[-3]]⟩]

/-- ★ **THE ONE LOOP CHECK for `ZZ/3`** — both residues, wraparound included:
`loop[0]·loop[1] = 0·(−3) = 0` (`natRemainder 1 2 = 1`, first factor `0`) and
`loop[1]·loop[0] = (−3)·0 = 0` (`natRemainder 2 2 = 0`, second factor `0`).  Degenerate-by-zero-factor
(the even boundary `[[0]]` kills each composition), honestly. -/
theorem cyclicThreePeriodicLoopComposesToZero :
    ∀ i, i < 2 →
      (listGetWithDefault (⟨[]⟩ : IntMatrix) cyclicThreePeriodicLoopBoundaries i).entryAt 0 0 *
      (listGetWithDefault (⟨[]⟩ : IntMatrix) cyclicThreePeriodicLoopBoundaries
        (natRemainder (i + 1) 2)).entryAt 0 0 = 0
  | 0, _ => by
      rw [show natRemainder (0 + 1) 2 = 1 from natRemainderOfLt (by decide)]
      exact intZeroMul _
  | 1, _ => by
      rw [show natRemainder (1 + 1) 2 = 0 from natRemainderSelf (by decide)]
      exact intMulZero _
  | _ + 2, iBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc iBound)))

/-- ★ **The 2-periodic group-homology tower of `ZZ/3`** — the loop `[ [[0]] , [[-3]] ]`, period 2, all
obligations discharged from the ONE loop check. -/
def cyclicThreePeriodicTower : PeriodicTower where
  loopBoundaries := cyclicThreePeriodicLoopBoundaries
  period := 2
  periodPositive := by decide
  loopMatchesLength := rfl
  loopRectangular := fun i iBound =>
    match i, iBound with
    | 0, _ => ⟨rfl, rfl, True.intro⟩
    | 1, _ => ⟨rfl, rfl, True.intro⟩
    | _ + 2, iBound =>
        Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc iBound)))
  firstBoundaryVanishes := rfl
  loopComposesToZero := cyclicThreePeriodicLoopComposesToZero

/-- The produced `ZZ/3` augmented directed complex — the NON-TRUNCATED chain complex (rank 1 at every
degree). -/
def cyclicThreePeriodicTowerChainComplex : AugmentedDirectedComplex :=
  cyclicThreePeriodicTower.toAugmentedDirectedComplex

/-- ★ **`d d = 0` for the `ZZ/3` tower at EVERY degree** — the finite ONE loop check lifted to all
infinitely many degrees, read off the produced ADC. -/
theorem cyclicThreePeriodicTowerBoundaryComposesToZero
    (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < cyclicThreePeriodicTowerChainComplex.basisCount dim)
    (colBound : colIndex < cyclicThreePeriodicTowerChainComplex.basisCount (dim + 2)) :
    sumOverIndices (cyclicThreePeriodicTowerChainComplex.basisCount (dim + 1)) (fun middleIndex =>
      (cyclicThreePeriodicTowerChainComplex.boundaryMatrix dim).entryAt rowIndex middleIndex *
      (cyclicThreePeriodicTowerChainComplex.boundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  cyclicThreePeriodicTower.chainComplexBoundaryComposesToZero dim rowIndex colIndex rowBound colBound

/-- ★ **The `ZZ/3` periodicity certificate** — `boundaryMatrix (dim + 2) = boundaryMatrix dim`, the
2-periodicity of the resolution, as a corollary of the generic `boundaryPeriodicity`. -/
theorem cyclicThreePeriodicTowerBoundaryPeriodicity (dim : Nat) :
    cyclicThreePeriodicTower.boundaryMatrix (dim + 2) = cyclicThreePeriodicTower.boundaryMatrix dim :=
  cyclicThreePeriodicTower.boundaryPeriodicity dim

/-! ### The boundary parity over the actual tower (the truth probe, PROBED at degree 10) -/

/-- `natRemainder (2·half) 2 = 0` — the even residue, via `natRemainderUnique` (`2·half = 2·half + 0`). -/
theorem natRemainderTwoOfDouble (half : Nat) : natRemainder (2 * half) 2 = 0 :=
  natRemainderUnique (by decide) (Nat.add_zero (2 * half)).symm

/-- `natRemainder (2·half + 1) 2 = 1` — the odd residue, via `natRemainderUnique`
(`2·half + 1 = 2·half + 1`). -/
theorem natRemainderTwoOfDoubleSucc (half : Nat) : natRemainder (2 * half + 1) 2 = 1 :=
  natRemainderUnique (by decide) rfl

/-- **The tower's boundary at every EVEN degree is `[[0]]`** — `∂_{even index} = (t−1) ↦ 0`, over the
actual tower. -/
theorem cyclicThreeTowerBoundaryOfEvenDegree (half : Nat) :
    cyclicThreePeriodicTower.boundaryMatrix (2 * half) = ⟨[[0]]⟩ :=
  congrArg (listGetWithDefault (⟨[]⟩ : IntMatrix) cyclicThreePeriodicLoopBoundaries)
    (natRemainderTwoOfDouble half)

/-- **The tower's boundary at every ODD degree is `[[-3]]`** — `∂_{odd index} = N ↦ 3`, over the actual
tower. -/
theorem cyclicThreeTowerBoundaryOfOddDegree (half : Nat) :
    cyclicThreePeriodicTower.boundaryMatrix (2 * half + 1) = ⟨[[-3]]⟩ :=
  congrArg (listGetWithDefault (⟨[]⟩ : IntMatrix) cyclicThreePeriodicLoopBoundaries)
    (natRemainderTwoOfDoubleSucc half)

/-- ★ **Truth probe at degree 10** (`= 2·5`): `boundaryMatrix 10 = [[0]]` — the tower is alive and even
far past the Squier carrier's degree-3 truncation. `rfl`. -/
theorem cyclicThreeTowerBoundaryAtDegreeTen :
    cyclicThreePeriodicTower.boundaryMatrix 10 = ⟨[[0]]⟩ := rfl

/-- ★ **Truth probe at degree 11** (`= 2·5 + 1`): `boundaryMatrix 11 = [[-3]]` — odd degree, the `N ↦ 3`
boundary. `rfl`. -/
theorem cyclicThreeTowerBoundaryAtDegreeEleven :
    cyclicThreePeriodicTower.boundaryMatrix 11 = ⟨[[-3]]⟩ := rfl

/-! ## B3 — the all-degrees homology read-off (`H0 = ZZ, H_odd = ZZ/3, H_even>0 = 0`)

The SNF of `boundaryMatrix dim` is degree-independent within a parity class (period 2): `SNF([[0]]) =
[[0]]` (rank 0) at even degrees, `SNF([[-3]]) = [[3]]` (rank 1, factor 3) at odd degrees — the shipped
cyclic seed's `cyclicThreeSmithNormalFormOfDim{Zero,One}`, whose reduction certificates certify these
literals ARE the tower's boundary SNFs.  Feeding them into the shipped generic
`SmithHomologyData.homologyInvariant` gives the parity pattern. -/

/-- **Every even-degree tower boundary reduces to its SNF `[[0]]`** — the shipped empty certificate,
applied to the ACTUAL tower boundary (rewritten by the even-parity lemma).  Rank 0. -/
theorem cyclicThreeTowerEvenBoundaryReducesToSmith (half : Nat) :
    cyclicThreeBoundaryOfDimZeroSmithCertificate.reducesToSmithForm
      (cyclicThreePeriodicTower.boundaryMatrix (2 * half)) 1 1 :=
  (cyclicThreeTowerBoundaryOfEvenDegree half).symm ▸ cyclicThreeBoundaryOfDimZeroReducesToSmith

/-- **Every odd-degree tower boundary reduces to its SNF `[[3]]`** — the shipped negate-column
certificate, applied to the ACTUAL tower boundary `[[-3]]`.  Rank 1, invariant factor `3` — the `ZZ/3`
torsion source at every odd degree. -/
theorem cyclicThreeTowerOddBoundaryReducesToSmith (half : Nat) :
    cyclicThreeBoundaryOfDimOneSmithCertificate.reducesToSmithForm
      (cyclicThreePeriodicTower.boundaryMatrix (2 * half + 1)) 1 1 :=
  (cyclicThreeTowerBoundaryOfOddDegree half).symm ▸ cyclicThreeBoundaryOfDimOneReducesToSmith

/-- The Smith data at an ODD degree: `SNF(∂_k) = [[0]]` (even index, rank 0), `SNF(∂_{k+1}) = [[3]]` (odd
index, rank 1, factor 3).  Field-identical to the shipped `cyclicThreeDegreeOneSmithData`. -/
def cyclicThreeTowerOddDegreeSmithData : SmithHomologyData :=
  { chainBasisCount := 1
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimZero
  , windowIntoLower := 1
  , smithBoundaryFromHigher := cyclicThreeSmithNormalFormOfDimOne
  , windowFromHigher := 1 }

/-- The Smith data at an EVEN degree `> 0`: `SNF(∂_k) = [[3]]` (odd index, rank 1), `SNF(∂_{k+1}) = [[0]]`
(even index, rank 0) — the opposite parity phase from the odd-degree data. -/
def cyclicThreeTowerEvenPositiveDegreeSmithData : SmithHomologyData :=
  { chainBasisCount := 1
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimOne
  , windowIntoLower := 1
  , smithBoundaryFromHigher := cyclicThreeSmithNormalFormOfDimZero
  , windowFromHigher := 1 }

/-- The Smith data at degree 0: no `∂₀` (the `[[0]]` placeholder gives `nullity = C_0 = 1`),
`SNF(∂₁) = [[0]]` (rank 0) — so `freeRank = 1`, `H0 = ZZ`, the augmentation-degree special case. -/
def cyclicThreeTowerDegreeZeroSmithData : SmithHomologyData :=
  { chainBasisCount := 1
  , smithBoundaryIntoLower := cyclicThreeSmithNormalFormOfDimZero
  , windowIntoLower := 1
  , smithBoundaryFromHigher := cyclicThreeSmithNormalFormOfDimZero
  , windowFromHigher := 1 }

/-- **The Smith data at any degree**, selected by parity (period-2 phase, degree 0 special).  Structural
recursion `degree + 3 ↦ degree + 1` keeps the odd/even phase. -/
def cyclicThreeTowerHomologyDataAtDegree : Nat → SmithHomologyData
  | 0 => cyclicThreeTowerDegreeZeroSmithData
  | 1 => cyclicThreeTowerOddDegreeSmithData
  | 2 => cyclicThreeTowerEvenPositiveDegreeSmithData
  | degree + 3 => cyclicThreeTowerHomologyDataAtDegree (degree + 1)

/-- **The homology invariant at any degree** — the shipped generic read-off applied to the parity Smith
data. -/
def cyclicThreeTowerHomologyInvariantAtDegree (degree : Nat) : HomologyInvariant :=
  (cyclicThreeTowerHomologyDataAtDegree degree).homologyInvariant

/-- **The odd-degree tower Smith data IS the shipped cyclic-3 degree-1 Smith data** — `rfl`.  The
tower's odd-degree homology reuses the shipped `H1(cyclic Z/3)` computation verbatim, not a fresh
literal. -/
theorem cyclicThreeTowerOddDegreeSmithDataIsShipped :
    cyclicThreeTowerOddDegreeSmithData = cyclicThreeDegreeOneSmithData := rfl

/-- ★ **`H0 = ZZ`** — `freeRank 1`, no torsion (the augmentation-degree special case: `nullity(C_0) = 1`,
`rank(∂₁) = 0`). -/
theorem cyclicThreeTowerDegreeZeroHomologyIsIntegers :
    cyclicThreeTowerHomologyInvariantAtDegree 0 = ⟨1, []⟩ := rfl

/-- ★★ **`H_odd = ZZ/3` AT EVERY ODD DEGREE** — `∀ half, H_{2·half+1} = ⟨0, [3]⟩`.  Free rank `0`,
invariant factor `3`, read off the parity Smith data by structural recursion on the half-index (period-2
phase collapse `degree+3 ↦ degree+1`).  Infinitely many `ZZ/3` torsion summands — the tower's genuine
odd-torsion content, unreachable by the truncated Squier carrier. -/
theorem cyclicThreeTowerOddDegreeHomologyIsZmodThree :
    ∀ half, cyclicThreeTowerHomologyInvariantAtDegree (2 * half + 1) = ⟨0, [3]⟩
  | 0 => rfl
  | half + 1 => cyclicThreeTowerOddDegreeHomologyIsZmodThree half

/-- ★ **`H_{even>0} = 0` AT EVERY POSITIVE EVEN DEGREE** — `∀ half, H_{2·half+2} = ⟨0, []⟩`.  Free rank
`0`, no torsion (`∂_k` injective, `∂_{k+1} = 0`), by structural recursion on the half-index. -/
theorem cyclicThreeTowerEvenPositiveDegreeHomologyIsZero :
    ∀ half, cyclicThreeTowerHomologyInvariantAtDegree (2 * half + 2) = ⟨0, []⟩
  | 0 => rfl
  | half + 1 => cyclicThreeTowerEvenPositiveDegreeHomologyIsZero half

/-- ★ **Homology truth probe at degree 9** (odd): `H9 = ZZ/3`. `rfl`. -/
theorem cyclicThreeTowerHomologyAtDegreeNine :
    cyclicThreeTowerHomologyInvariantAtDegree 9 = ⟨0, [3]⟩ := rfl

/-- ★ **Homology truth probe at degree 10** (even `> 0`): `H10 = 0`. `rfl`. -/
theorem cyclicThreeTowerHomologyAtDegreeTen :
    cyclicThreeTowerHomologyInvariantAtDegree 10 = ⟨0, []⟩ := rfl

/-- ★ **Homology truth probe at degree 11** (odd): `H11 = ZZ/3`. `rfl`. -/
theorem cyclicThreeTowerHomologyAtDegreeEleven :
    cyclicThreeTowerHomologyInvariantAtDegree 11 = ⟨0, [3]⟩ := rfl

/-! ## B4 — the bridge to the walker complex, the non-truncation witness, and the honest ledger -/

/-- ★ **AGREEMENT AT `H1` with the shipped Squier walker complex.**  The tower's degree-1 homology
invariant equals the shipped `cyclicThreeDegreeOneHomologyInvariant` (`= ⟨0, [3]⟩`) — both compute
`H1(ZZ/3) = ZZ/3`.  `rfl`.  The two complexes DIFFER (Squier truncated at 3, tower 2-periodic) but
COINCIDE at degree 1, the shared `ZZ/3` headline. -/
theorem cyclicThreePeriodicTowerAgreesWithWalkerAtDegreeOne :
    cyclicThreeTowerHomologyInvariantAtDegree 1 = cyclicThreeDegreeOneHomologyInvariant := rfl

/-- ★ **AGREEMENT AT `H2` (`= 0`) with the shipped walkers.**  The tower's degree-2 homology invariant
equals the canonical `walkingMonadDegreeTwoHomologyInvariant` (`= ⟨0, []⟩`) — matching the shipped
cyclic-3 `H2 = 0` (`cyclicThreeDegreeTwoHomologyIsZero`).  `rfl`. -/
theorem cyclicThreePeriodicTowerAgreesWithWalkerAtDegreeTwo :
    cyclicThreeTowerHomologyInvariantAtDegree 2 = walkingMonadDegreeTwoHomologyInvariant := rfl

/-- ★ **THE DIVERGENCE POINT `H3`.**  The tower's `H3 = ZZ/3` (`⟨0, [3]⟩`) — the TRUE group homology
`H3(ZZ/3)`.  The shipped Squier walker's `H3` is instead the degenerate truncation artifact `ker d3 =
ZZ²` (`cyclicThreeBasisCount 3 = 2`, no `d4`).  Same monoid `ZZ/3`, chain-homotopy-equivalent complexes,
but DIFFERENT `H3` values are computed — the tower's is the homologically-honest one.  `rfl`. -/
theorem cyclicThreeTowerHomologyAtDegreeThree :
    cyclicThreeTowerHomologyInvariantAtDegree 3 = ⟨0, [3]⟩ := rfl

/-- ★ **THE NON-TRUNCATION WITNESS.**  The produced ADC has a nonzero basis atom (`= 1`) at EVERY degree
— the escape from the Squier carrier's degree-3 truncation (`SquierNoGoInterface`'s
`carrierDegreeThreeChainIsAlwaysFinite`: the List carrier has `basisCount 3 = criticalPairs.length` and
`basisCount ≥ 4 = 0`).  This is what lets the tower even STATE `H_k` at all `k`. -/
theorem cyclicThreePeriodicTowerBasisIsNonzeroAtEveryDegree :
    ∀ dim, cyclicThreePeriodicTowerChainComplex.basisCount dim = 1 :=
  fun _ => rfl

/-- The shipped Squier walker carrier TRUNCATES: `cyclicThreeBasisCount 4 = 0`. `rfl`. -/
theorem cyclicThreeWalkerCarrierTruncatesAtDegreeFour : cyclicThreeBasisCount 4 = 0 := rfl

/-- ★ **The crisp truncation contrast at degree 4** — the SAME degree where the Squier carrier is dead
(`cyclicThreeBasisCount 4 = 0`), the periodic tower is ALIVE (`basisCount 4 = 1`).  The two complexes
are genuinely different objects. `rfl`. -/
theorem cyclicThreePeriodicTowerIsAliveAtDegreeFour :
    cyclicThreePeriodicTowerChainComplex.basisCount 4 = 1 := rfl

/-! ### Honest scope statement (for the ledger)

The shipped `Homology/CyclicThreeChainComplex` computes the PRESENTATION (Squier polygraphic) homology of
`⟨s | sss ⟹ id⟩` TRUNCATED at degree 3 (critical PAIRS only, no critical triples); this module is the
GROUP-HOMOLOGY resolution of `ZZ/3` (Brown, *Cohomology of Groups* Ch. I §6 & Ch. VI).  Both resolve `ZZ`
over `ZZ[ZZ/3]`, so by the fundamental lemma of homological algebra they are chain-homotopy equivalent and
share `H_*` — but as CHAIN COMPLEXES they differ (Squier larger and truncated; periodic minimal and
2-periodic).  They COINCIDE in degrees 0, 1, 2 (`H0 = ZZ`, `H1 = ZZ/3`, `H2 = 0` — the machine-checked
`AgreesWithWalkerAtDegree{One,Two}`) and DIVERGE at/above degree 3: the walker's `H3 = ker d3 = ZZ²` is a
truncation artifact, the tower's `H3 = ZZ/3` is the true group homology.  The chain-homotopy equivalence
itself is NOT formalised (the honest residual).  Cite: Squier 1987 (JPAA 49); Guiraud–Malbos (polygraphic
resolutions).

The SQUIER-NOGO escape route (the vacuity finding's named exit): the FUNCTION carrier `basisCount = fun _
=> 1` breaks the List carrier's degree-3 truncation ceiling
(`SquierNoGoInterface.carrierDegreeThreeChainIsAlwaysFinite`), so the GRADED homology `⊕_{k} H_k = ZZ ⊕
(⊕_{k odd} ZZ/3)` is infinitely generated as an abelian group (`cyclicThreeTowerOddDegreeHomologyIsZmodThree`
gives a nonzero `ZZ/3` at infinitely many degrees).  DOUBLE CAVEAT: truncation escaped, per-degree RANK
finiteness NOT — each `H_k` is f.g. (`C_k = ZZ^1`); Squier's `S_1` needs infinite rank at ONE degree
(`basisCount → ∞`), which no `Nat`-valued `basisCount` expresses, so the periodic tower does NOT witness
`S_1` — the no-go's obligation-3 (`homologicalNonFinitenessStatus = walledByCarrierFiniteness`) STAYS
walled.  Named: "periodic tower = non-truncated, still rank-finite; graded homology infinitely generated,
each graded piece f.g." -/

/-- ★ **The TOWER-PERIODIC (#2146) ledger marker.**  What stands, zero-axiom: the generic `PeriodicTower`
carrier producing a NON-TRUNCATED `AugmentedDirectedComplex` from ONE loop of boundary data + the
periodicity certificate (`PeriodicTower.boundaryPeriodicity`); the finite-check-to-infinite-conclusion
`d d = 0` at every degree from the ONE loop check (`cyclicThreePeriodicTowerBoundaryComposesToZero`); the
all-degrees read-off `H0 = ZZ` / `H_odd = ZZ/3` / `H_{even>0} = 0`
(`cyclicThreeTowerOddDegreeHomologyIsZmodThree`, probed at degrees 9/10/11); the honest bridge to the
Squier walker complex (agree at `H0`/`H1`/`H2`, differ at `H3`, chain-homotopy equivalence NOT formalised);
and the SQUIER-NOGO escape (degree-truncation broken, rank-finiteness NOT — `S_1` stays walled).  Read the
meaning from THIS docstring (the honest-record convention). -/
def towerPeriodicHomologyLedgerIsComplete : Bool := true

/-- ★ **The honest DOUBLE-CAVEAT marker for the Squier-no-go escape.**  The periodic tower escapes the
List carrier's DEGREE truncation (nonzero basis at every degree) but NOT per-degree RANK finiteness; it
witnesses graded-homology infinite-generation, NOT the infinite-rank-at-one-degree that Squier's `S_1`
requires — so `SquierNoGoInterface`'s obligation-3 wall stays intact.  `= true`. -/
def towerPeriodicSquierEscapeStaysScoped : Bool := true

end FX1Poly.Polygraph.Homology
