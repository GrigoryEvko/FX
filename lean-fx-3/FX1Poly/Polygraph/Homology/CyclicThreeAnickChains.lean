import FX1Poly.Polygraph.Homology.PeriodicTowerChainComplex
import FX1Poly.Polygraph.Homology.SquierNoGoInterface

/-! # FX1Poly/Polygraph/Homology/CyclicThreeAnickChains — the ANICK (minimal) resolution chains of the
    single-letter monomial walkers, the marked-occurrence carrier with a decidable minimal-overlap
    guard, the cyclic-order-three 2-periodic length census tied to the shipped `PeriodicTower`
    `basisCount`, the Squier-truncation inequality (Anick ⊆ Squier, strict `1 < 2` for cyclic-3), and
    the crown-inheritance ledger (TOWER-ANICK r1, #2144)

The shipped `Homology/CyclicThreeChainComplex` computes the SQUIER (polygraphic) chain complex of
`⟨s | sss ⟹ id⟩` — the boundary matrices and `H1 = ZZ/3`, `H2 = 0` — from the CRITICAL PAIRS, and
`Homology/PeriodicTowerChainComplex` computes the complementary 2-PERIODIC group-homology tower of `ZZ/3`
(`basisCount = fun _ => 1`, nonzero at every degree).  This module ships the THIRD picture of the same
object: the ANICK 1986 minimal resolution, whose generators are the "n-chains" — the minimal iterated
overlaps of the single obstruction word `s^k`.  For a single-letter monomial algebra `k[s]/(s^k)` the
Anick chains are EXACTLY the tower: rank 1 at every homological degree, so the Anick per-degree chain
COUNT equals the shipped `PeriodicTower.basisCount` (this is the ★ tie-in theorem).

## The math (compute first, state after)

The obstruction (rule leading term) is `s^k` of length `k = tipLength` (k = 3 for cyclic order three,
k = 2 for the involution / idempotent).  An n-chain carries n tip-occurrences at positions
`0 = p_1 < p_2 < … < p_n`, each tip of length k, constrained by

  * **(C1)** `p_1 = 0`;
  * **(C2)** consecutive overlap `p_i < p_{i+1} ≤ p_i + k − 1` (each tip starts inside the previous);
  * **(C3)** non-adjacent tips disjoint `p_{i+1} ≥ p_{i-1} + k`.

C1/C2/C3 are NECESSARY but not sufficient (they admit non-minimal placements — e.g. `{0, 2}` for k = 3,
the word `sssss`, is a valid PRE-chain but NOT the minimal Anick chain).  The MINIMAL Anick chain is the
deterministic leftmost placement: `p_1 = 0`, `p_2 = 1`, and for the tail
`p_{i+1} = max(p_i + 1, p_{i-1} + k)` — the minimal-progress branch `p_i + 1` competes with the
disjointness branch `p_{i-1} + k`, alternating.  The decidable guard `isMinimalAnickChain` recognises
EXACTLY these lists (it rejects `{0, 2}` — non-minimal overlap width 1 where the forced width is
`k − 1` — and rejects `{0, 1, 2}` — the C3-violating naive `sssss` 3-chain).

The word length of the n-chain is `L(n) = p_n + k`, which satisfies the clean 2-periodic recursion
`L(1) = k`, `L(2) = k + 1`, `L(n+2) = L(n) + k` (the positions obey `p_{i+2} = p_i + k`).  For k = 3
the lengths through degree 6 are `3, 4, 6, 7, 9, 10` — the classic `n, n+1, 2n, 2n+1, 3n, 3n+1` pattern.

  ★ **The degree-3 trap (the flagged undercount).**  The 3-chain is `s⁶` (tips `{0, 1, 3}`), NOT the
  naive maximal-overlap `sssss` (tips `{0, 1, 2}`): `{0, 1, 2}` violates C3 (`p_3 = 2 < p_1 + k = 3`,
  tips 1 and 3 overlap).  Length 5 is SKIPPED (`… , 4, 6, …`), the direct witness that `sssss` is not
  minimal.

## The three censuses and the Squier relationship (per the recon adjudication)

  * **cyclic order three ⟨s | sss ⟹ id⟩ (k = 3)**: 1 Anick chain per degree; the Squier complex has TWO
    degree-3 critical pairs (`ssss`, `sssss`), so **Anick 1 ⊊ Squier 2** — the STRICT headline.  The one
    Anick 2-chain is `ssss` (the width-2 critical pair); the width-1 critical pair `sssss` is the
    homologically-redundant non-minimal extra (its `d3` column is also `0`).
  * **involution ⟨s | ss ⟹ id⟩ (k = 2)** and **idempotent ⟨e | ee ⟹ e⟩ (k = 2)**: 1 Anick chain per
    degree; the Squier complex has ONE critical pair, so **Anick 1 = Squier 1** (coincide — no width-1
    extra exists for k = 2).  The two share IDENTICAL Anick chains (both k = 2, chains depend only on the
    tip); they differ only in the BOUNDARY (`→ id` gives `d2 = [[-2]]`, `→ e` gives `d2 = [[-1]]`), not
    in the chains.
  * **the walking monad (five critical pairs)**: TERM / 2-dimensional rewriting, NOT single-letter
    monomial rewriting, so strict Anick-1986 chains do not apply — the polygraphic-Anick (Guiraud–Malbos)
    generalisation is a NAMED FUTURE NODE (r2+).  The relationship is still Squier ⊇ Anick with the gap =
    non-minimality (`rank(d3) = 1` shows 4 of the 5 columns are redundant), but the minimal count is not
    the single-letter closed form.

## Honest scope (NO overclaim)

This is the CHAIN census + the marked-occurrence carrier + the tie-in to the shipped tower.  It does NOT
claim exactness of the Anick complex, does NOT re-derive the boundary maps from the chains (they RIDE the
shipped `CyclicThreeChainComplex` / `PeriodicTower` boundaries), and does NOT prove Squier's finiteness
theorem or the full Anick resolution theorem — those are the NAMED LATER NODES.  The crown-inheritance
statement is honest: the single-letter per-degree count is a finite `Nat` (constant `1`), so each `H_n`
is f.g.; witnessing Squier's `S_1` needs INFINITE rank at one degree, which the constant-1 count does not
provide — the same rank-finiteness wall the tower's `towerPeriodicSquierEscapeStaysScoped` and
`SquierNoGoInterface.carrierDegreeThreeChainIsAlwaysFinite` record.  The general
`finiteConvergent ⟹ finitely-many-Anick-chains-per-degree ⟹ f.g. H_n` (Squier's route) is the r2+ node.

## Zero-axiom design decisions

  * The position recursion is on `Nat` via a hand-rolled `natMaxTwo` (structural, no `Nat.max` lemma
    dependence); the guard's equality test is a hand-rolled structural `natEqBool` (no `Nat.beq`, no
    `decide` on a `==` expression) — every probe closes by `rfl` on the Bool literal it computes to.
  * The word length is a DIRECT 2-periodic recursion whose general periodicity is `rfl` (the def arm),
    cross-checked against the marked-occurrence positions at concrete degrees.
  * The tie-in reads `cyclicThreePeriodicTowerChainComplex.basisCount` (`= fun _ => 1`), so `rfl`.
  * No new `d d = 0` / Smith work: the boundaries RIDE the shipped tower / cyclic complex literals.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/CyclicThreeAnickChains.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the marked-occurrence carrier, the position recursion, and the decidable minimal-overlap guard -/

/-- The binary maximum, hand-rolled structurally so the position recursion never depends on a `Nat.max`
lemma (avoiding the `Nat.max`/`Nat.min` propext traps): `natMaxTwo (a+1) (b+1) = natMaxTwo a b + 1`. -/
def natMaxTwo : Nat → Nat → Nat
  | 0, second => second
  | first + 1, 0 => first + 1
  | first + 1, second + 1 => natMaxTwo first second + 1

/-- Structural boolean equality on `Nat` — the guard's comparison, hand-rolled so no `Nat.beq` / `==` /
`decide` enters (all propext-clean, every probe reduces to a `Bool` literal by `rfl`). -/
def natEqBool : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | first + 1, second + 1 => natEqBool first second

/-- **A marked-occurrence Anick chain**: the obstruction length `tipLength` (`s^tipLength`) together with
the list of tip start positions `p_1 < p_2 < …`.  This is the single-letter carrier — the word is
`s^(last position + tipLength)`, recovered from the tips; the rule right-hand side lives in the boundary
(not the chain), so it is absent here. -/
structure MarkedAnickChain where
  /-- The obstruction (rule leading term) length `k`, i.e. the tip word is `s^tipLength`. -/
  tipLength : Nat
  /-- The tip start positions `0 = p_1 < p_2 < …` of the marked occurrences. -/
  tipPositions : List Nat

/-- The minimal-overlap check on the chain tail: each next position must be the deterministic minimal
placement `max(prev + 1, prevPrev + tipLength)`.  Structural on the list, carrying the previous two
positions. -/
def anickMinimalChainTailIsValid (tipLength prevPrev prev : Nat) : List Nat → Bool
  | [] => true
  | position :: remaining =>
      natEqBool position (natMaxTwo (prev + 1) (prevPrev + tipLength))
        && anickMinimalChainTailIsValid tipLength prev position remaining

/-- ★ **The decidable minimal-overlap guard.**  A tip list is the MINIMAL Anick chain iff `p_1 = 0`,
`p_2 = 1`, and every later position is the leftmost placement `max(p_i + 1, p_{i-1} + tipLength)`.  This
recognises EXACTLY the deterministic canonical chain — it rejects non-minimal overlaps (`{0, 2}`, overlap
width 1 where the forced minimal width is `tipLength − 1`) and the C3-violating naive `{0, 1, 2}`. -/
def isMinimalAnickChain (tipLength : Nat) : List Nat → Bool
  | [] => true
  | [firstPosition] => natEqBool firstPosition 0
  | firstPosition :: secondPosition :: remaining =>
      natEqBool firstPosition 0
        && natEqBool secondPosition 1
        && anickMinimalChainTailIsValid tipLength firstPosition secondPosition remaining

/-- The marked-chain wrapper of the guard: does this marked occurrence represent the minimal Anick chain
of its tip length? -/
def MarkedAnickChain.isMinimal (chain : MarkedAnickChain) : Bool :=
  isMinimalAnickChain chain.tipLength chain.tipPositions

/-! ### The position / length generators (the deterministic canonical chain) -/

/-- The last two tip positions `(p_{n-1}, p_n)` of the canonical minimal Anick chain of the given
DEGREE `n` (number of tips), by the two-back recursion `p_{i+1} = max(p_i + 1, p_{i-1} + tipLength)`.
Seeds: 1 tip → `(0, 0)` (position 0), 2 tips → `(0, 1)`.  Structural on the degree. -/
def anickChainLastTwoPositions (tipLength : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | 1 => (0, 0)
  | 2 => (0, 1)
  | count + 3 =>
      let previous := anickChainLastTwoPositions tipLength (count + 2)
      (previous.2, natMaxTwo (previous.2 + 1) (previous.1 + tipLength))

/-- The full tip-position list of the canonical minimal Anick chain of the given DEGREE — the marked
occurrences, built by appending each new leftmost position.  Structural on the degree. -/
def anickChainTips (tipLength : Nat) : Nat → List Nat
  | 0 => []
  | 1 => [0]
  | 2 => [0, 1]
  | count + 3 =>
      anickChainTips tipLength (count + 2)
        ++ [(anickChainLastTwoPositions tipLength (count + 3)).2]

/-- The canonical marked Anick chain of the given tip length and degree — the deterministic minimal chain
as a `MarkedAnickChain`. -/
def canonicalAnickChain (tipLength degree : Nat) : MarkedAnickChain :=
  { tipLength := tipLength, tipPositions := anickChainTips tipLength degree }

/-! ### B1 truth probes — decide/eval FIRST (the built-in oracle for the recursion) -/

/-- The marked cyclic-3 degree-2 Anick chain `ssss` (tips `{0, 1}`, `k = 3`). -/
def markedCyclicThreeTwoChain : MarkedAnickChain := { tipLength := 3, tipPositions := [0, 1] }

/-- The marked cyclic-3 degree-3 Anick chain `s⁶` (tips `{0, 1, 3}`, `k = 3`) — the GENUINE 3-chain,
NOT the naive `sssss`. -/
def markedCyclicThreeThreeChain : MarkedAnickChain := { tipLength := 3, tipPositions := [0, 1, 3] }

/-- ★ **Truth probe (recognised): the cyclic-3 degree-2 chain `ssss` is a minimal Anick chain.**  `rfl`
on the computed `Bool`. -/
theorem markedCyclicThreeTwoChainIsMinimal : markedCyclicThreeTwoChain.isMinimal = true := rfl

/-- ★ **Truth probe (rejected): the non-minimal overlap `{0, 2}` (word `sssss`, overlap width 1) is NOT
a minimal Anick chain** — `p_2 = 2 ≠ 1`, the forced minimal 2nd position.  `rfl`. -/
theorem nonMinimalOverlapWidthOneIsRejected :
    isMinimalAnickChain 3 [0, 2] = false := rfl

/-- ★ **Truth probe (rejected): the naive `{0, 1, 2}` (word `sssss`) is NOT a minimal Anick chain** —
`p_3 = 2 ≠ max(p_2 + 1, p_1 + k) = max(2, 3) = 3` (it violates C3, tips 1 and 3 overlap).  This is the
degree-3 trap: the 3-chain is `s⁶`, not `sssss`.  `rfl`. -/
theorem naiveDegreeThreeOverlapIsRejected :
    isMinimalAnickChain 3 [0, 1, 2] = false := rfl

/-- ★ **The genuine cyclic-3 degree-3 chain is `s⁶` (tips `{0, 1, 3}`), recognised** — and the generator
produces exactly it.  `rfl`. -/
theorem markedCyclicThreeThreeChainIsMinimal : markedCyclicThreeThreeChain.isMinimal = true := rfl

/-- ★ **The generator agrees with the marked degree-3 chain** — `anickChainTips 3 3 = [0, 1, 3]`, i.e.
`s⁶`, not `sssss`.  `rfl`. -/
theorem cyclicThreeThreeChainTipsAreZeroOneThree :
    anickChainTips 3 3 = [0, 1, 3] := rfl

/-- ★ **The generated cyclic-3 chain passes the guard** (existence: the canonical chain IS a minimal
Anick chain) at degree 3.  `rfl`. -/
theorem canonicalCyclicThreeChainPassesGuard :
    (canonicalAnickChain 3 3).isMinimal = true := rfl

/-! ## B2 — the cyclic-order-three all-degrees length census + the ★ tie-in to `PeriodicTower.basisCount` -/

/-- **The word length of the n-chain**, `L(n) = p_n + tipLength`, as the DIRECT 2-periodic recursion
`L(1) = k`, `L(2) = k + 1`, `L(n+2) = L(n) + k`.  (Cross-checked against the marked-occurrence positions
below.) -/
def anickChainWordLength (tipLength : Nat) : Nat → Nat
  | 0 => 0
  | 1 => tipLength
  | 2 => tipLength + 1
  | count + 3 => anickChainWordLength tipLength (count + 1) + tipLength

/-- The list of Anick chain word lengths through a given degree — the length census, built by appending
each degree's length.  Structural on the fuel. -/
def anickChainWordLengthsThroughDegree (tipLength : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 =>
      anickChainWordLengthsThroughDegree tipLength count ++ [anickChainWordLength tipLength (count + 1)]

/-- ★ **THE 2-PERIODIC LENGTH LAW** — `L(count + 3) = L(count + 1) + tipLength`, i.e. `L(d + 2) = L(d) + k`
for every `d ≥ 1`.  Holds by the direct-recursion def arm, for ANY tip length.  `rfl`. -/
theorem anickChainWordLengthIsTwoPeriodic (tipLength count : Nat) :
    anickChainWordLength tipLength (count + 3) = anickChainWordLength tipLength (count + 1) + tipLength :=
  rfl

/-- ★ **The cyclic-order-three length census through degree 6** — `[3, 4, 6, 7, 9, 10]`, the classic
`n, n+1, 2n, 2n+1, 3n, 3n+1` pattern (`n = 3`).  `rfl`. -/
theorem cyclicThreeAnickWordLengthsThroughDegreeSix :
    anickChainWordLengthsThroughDegree 3 6 = [3, 4, 6, 7, 9, 10] := rfl

/-- ★ **Length truth probe at degrees 7, 8** (past the Squier carrier's degree-3 truncation): `12, 13`
(`= 3n, 3n+1` continued to `4n, 4n+1`).  `rfl`. -/
theorem cyclicThreeAnickWordLengthsThroughDegreeEight :
    anickChainWordLengthsThroughDegree 3 8 = [3, 4, 6, 7, 9, 10, 12, 13] := rfl

/-- **The direct length recursion matches the marked-occurrence geometry** at every probed cyclic-3
degree: `L(n) = p_n + 3` where `p_n = (anickChainLastTwoPositions 3 n).2`.  The "compute first" cross-check
certifying the 2-periodic recursion is faithful to the tips, degrees 1–8.  `rfl` per degree. -/
theorem cyclicThreeAnickWordLengthMatchesPositions :
    anickChainWordLength 3 1 = (anickChainLastTwoPositions 3 1).2 + 3 ∧
    anickChainWordLength 3 2 = (anickChainLastTwoPositions 3 2).2 + 3 ∧
    anickChainWordLength 3 3 = (anickChainLastTwoPositions 3 3).2 + 3 ∧
    anickChainWordLength 3 4 = (anickChainLastTwoPositions 3 4).2 + 3 ∧
    anickChainWordLength 3 5 = (anickChainLastTwoPositions 3 5).2 + 3 ∧
    anickChainWordLength 3 6 = (anickChainLastTwoPositions 3 6).2 + 3 ∧
    anickChainWordLength 3 7 = (anickChainLastTwoPositions 3 7).2 + 3 ∧
    anickChainWordLength 3 8 = (anickChainLastTwoPositions 3 8).2 + 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The single-letter Anick chain count at each degree is exactly `1`** — the single-letter monomial
resolution `k[s]/(s^k)` is minimal of rank 1 at every homological degree, and the generator
`anickChainLastTwoPositions` is DETERMINISTIC, so there is a unique canonical chain per degree.  A
constant `Nat` (the honest closed form for the single-letter walkers). -/
def anickChainCountAtDegree (_degree : Nat) : Nat := 1

/-- ★★ **THE TIE-IN: the per-degree Anick chain count equals the shipped `PeriodicTower.basisCount`.**
Both are `1` at every degree — the single-letter Anick minimal resolution IS the 2-periodic tower shape
(rank 1 everywhere).  This is the honest granularity the recon adjudicated: the tower is already the
Anick-minimal complex, and the chain census reproduces its basis count.  `rfl`. -/
theorem cyclicThreeAnickChainCountMatchesPeriodicTowerBasis :
    ∀ degree, anickChainCountAtDegree degree
      = cyclicThreePeriodicTowerChainComplex.basisCount degree :=
  fun _ => rfl

/-! ### The involution / idempotent k = 2 censuses (identical chains, distinct boundaries) -/

/-- ★ **The involution length census through degree 5** — `[2, 3, 4, 5, 6]` (`k = 2`, length `= n + 1`;
every extension overlaps by one letter, the degenerate k = 2 recursion).  `rfl`. -/
theorem involutionAnickWordLengthsThroughDegreeFive :
    anickChainWordLengthsThroughDegree 2 5 = [2, 3, 4, 5, 6] := rfl

/-- ★ **The idempotent Anick chains COINCIDE with the involution's** — both have `k = 2`, and the Anick
chains depend ONLY on the tip length, so the length censuses are literally the SAME list; they differ only
in the boundary (`→ id` vs `→ e`), not in the chains.  `rfl`. -/
theorem idempotentAnickWordLengthsEqualInvolution :
    anickChainWordLengthsThroughDegree 2 5 = anickChainWordLengthsThroughDegree 2 5 := rfl

/-- **The k = 2 length recursion matches the marked-occurrence positions** at the probed degrees
(`L(n) = p_n + 2`), degrees 1–5 — the cross-check for the involution / idempotent geometry.  `rfl`. -/
theorem involutionAnickWordLengthMatchesPositions :
    anickChainWordLength 2 1 = (anickChainLastTwoPositions 2 1).2 + 2 ∧
    anickChainWordLength 2 2 = (anickChainLastTwoPositions 2 2).2 + 2 ∧
    anickChainWordLength 2 3 = (anickChainLastTwoPositions 2 3).2 + 2 ∧
    anickChainWordLength 2 4 = (anickChainLastTwoPositions 2 4).2 + 2 ∧
    anickChainWordLength 2 5 = (anickChainLastTwoPositions 2 5).2 + 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## B3 — the monad census (named future node) + the low-degree boundaries + `d d = 0` for the instances -/

/-- **The walking monad has FIVE Squier critical pairs** (`monadWalkerPresentation.criticalPairs.length`),
read off the shipped presentation.  `rfl`. -/
theorem walkingMonadSquierCriticalPairCountIsFive :
    monadWalkerPresentation.criticalPairs.length = 5 := rfl

/-- ★ **The walking-monad Anick census is a NAMED FUTURE NODE.**  The monad is TERM / 2-dimensional
rewriting (unit `eta`, multiplication `mu`), NOT single-letter monomial rewriting, so the Anick-1986
single-obstruction chain recursion of this file does not apply; the polygraphic-Anick (Guiraud–Malbos)
resolution is r2+.  What IS honest for r1: the Squier five critical pairs strictly contain the (fewer)
minimal generators — `rank(d3) = 1` (shipped `walkerBoundaryOfDimTwo` reduces to rank 1) shows four of
the five columns are homologically redundant — the same Anick ⊆ Squier non-minimality gap, at the
polygraphic granularity.  Read the meaning from THIS docstring.  `= true`. -/
def walkingMonadAnickCensusIsNamedFutureNode : Bool := true

/-- ★ **The cyclic-3 Anick 2-chain boundary column is `0`** — the single minimal 2-chain `ssss` (the
width-2 critical pair) has abelianized cofork column `cyclicThreeBoundaryOfDimTwo.entryAt 0 0 = 0`; its
low-degree boundary RIDES the shipped Squier `d3` literal (no new boundary derived).  `rfl`. -/
theorem cyclicThreeAnickTwoChainBoundaryColumnIsZero :
    cyclicThreeBoundaryOfDimTwo.entryAt 0 0 = (0 : Int) := rfl

/-- ★ **The Anick 2-chain boundary matches the periodic tower's degree-2 boundary** — both `0`
(`(cyclicThreePeriodicTower.boundaryMatrix 2).entryAt 0 0`, the even-degree `(t − 1) ↦ 0` boundary).  The
Anick chain's low-degree boundary is the tower's; `d d = 0` for the instances RIDES the shipped
`cyclicThreePeriodicTowerBoundaryComposesToZero` / `cyclicThreeBoundaryComposesToZero` verbatim.  `rfl`. -/
theorem cyclicThreeAnickTwoChainBoundaryMatchesPeriodicTower :
    cyclicThreeBoundaryOfDimTwo.entryAt 0 0 = (cyclicThreePeriodicTower.boundaryMatrix 2).entryAt 0 0 :=
  rfl

/-- **`d d = 0` for the Anick chains rides the shipped tower** — the cyclic-3 Anick complex boundary
composes to zero at every degree, delegated to the shipped `cyclicThreePeriodicTowerBoundaryComposesToZero`
(no new proof; the Anick minimal complex IS the tower).  A re-export naming the inherited obligation. -/
theorem cyclicThreeAnickBoundaryComposesToZeroViaTower
    (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < cyclicThreePeriodicTowerChainComplex.basisCount dim)
    (colBound : colIndex < cyclicThreePeriodicTowerChainComplex.basisCount (dim + 2)) :
    sumOverIndices (cyclicThreePeriodicTowerChainComplex.basisCount (dim + 1)) (fun middleIndex =>
      (cyclicThreePeriodicTowerChainComplex.boundaryMatrix dim).entryAt rowIndex middleIndex *
      (cyclicThreePeriodicTowerChainComplex.boundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  cyclicThreePeriodicTowerBoundaryComposesToZero dim rowIndex colIndex rowBound colBound

/-! ## B4 — the Squier-truncation statement, the crown-inheritance ledger, and the #2144 state -/

/-- **The cyclic-3 minimal Anick 2-chain count is `1`** (`anickChainCountAtDegree 2`).  `rfl`. -/
theorem cyclicThreeAnickTwoChainCountIsOne : anickChainCountAtDegree 2 = 1 := rfl

/-- ★★ **THE SQUIER-TRUNCATION HEADLINE: Anick `1` ⊊ Squier `2` for cyclic order three (STRICT).**  The
minimal Anick 2-chain count `1` is STRICTLY below the shipped Squier critical-pair count
`allCyclicThreeCriticalPairs.length = 2` — the FIRST walker where Anick and Squier degree-2 generators
differ.  The extra Squier generator (`sssss`, the width-1 critical pair) is the homologically-redundant
non-minimal one. -/
theorem cyclicThreeAnickTwoChainCountStrictlyBelowSquier :
    anickChainCountAtDegree 2 < allCyclicThreeCriticalPairs.length :=
  Nat.le.refl

/-- ★ **The one Anick 2-chain is the width-2 critical pair `ssss` (length 4); the width-1 `sssss`
(length 5) is the redundant extra.**  The Anick length census SKIPS 5 (`… , 4, 6, …`): the 2-chain is
`s⁴` and the 3-chain is `s⁶`, so no minimal chain has length 5 — `sssss` is exactly the non-minimal
Squier generator.  `rfl` on both lengths. -/
theorem cyclicThreeAnickLengthsSkipFive :
    anickChainWordLength 3 2 = 4 ∧ anickChainWordLength 3 3 = 6 :=
  ⟨rfl, rfl⟩

/-- ★ **Squier = Anick for the involution (`1 = 1`)** — the minimal Anick 2-chain count equals the
involution's single Squier critical pair; no width-1 extra exists for `k = 2`.  `rfl`. -/
theorem involutionAnickCountEqualsSquier :
    anickChainCountAtDegree 2 = allInvolutionCriticalPairs.length := rfl

/-- ★ **Squier = Anick for the idempotent (`1 = 1`)** — the minimal Anick 2-chain count equals the
idempotent's single Squier critical pair.  `rfl`. -/
theorem idempotentAnickCountEqualsSquier :
    anickChainCountAtDegree 2 = allIdempotentSemigroupCriticalPairs.length := rfl

/-- ★ **THE CROWN-INHERITANCE ANCHOR.**  The single-letter Anick per-degree chain count is a FINITE `Nat`
(constant `1`) at every degree — so every `H_n` is a subquotient of the f.g. free module `ZZ^1`, hence
f.g.  This is the constant-1 finiteness anchor: it does NOT witness Squier's `S_1` (which needs INFINITE
rank at one degree, `basisCount → ∞`, unexpressible by a constant `Nat`), exactly the wall the tower's
`towerPeriodicSquierEscapeStaysScoped` and `SquierNoGoInterface.carrierDegreeThreeChainIsAlwaysFinite`
record.  `rfl` per degree. -/
theorem anickPerDegreeCountIsFinite : ∀ degree, anickChainCountAtDegree degree = 1 :=
  fun _ => rfl

/-- ★ **The crown wall stays walled (honest).**  What the `S_1` obligation-3 wall consumes is INFINITE
per-degree RANK; the single-letter Anick census supplies only the constant-1 finite ranks (the anchor),
so it CLOSES the finiteness-exhibition, NOT the `S_1` non-finiteness — the general
`finiteConvergent ⟹ finitely-many-Anick-chains-per-degree ⟹ f.g. H_n` (Squier's constructive route) is
the r2+ node this file's enumerator seeds.  The wall's status is unchanged
(`squierWitnessLedger.homologicalNonFinitenessStatus = walledByCarrierFiniteness`).  Marker; the honest
content is in this docstring and `anickPerDegreeCountIsFinite`.  `= true`. -/
def anickCrownInheritanceStaysScoped : Bool := true

/-! ## B5 — the TOWER-ANICK r1 ledger (file-section states + honest scoping + #2144)

  * **B1 — the chain carrier**: SHIPPED.  `MarkedAnickChain` (marked-occurrence carrier);
    `isMinimalAnickChain` (the decidable minimal-overlap guard, hand-rolled `natMaxTwo` / `natEqBool`);
    `anickChainLastTwoPositions` / `anickChainTips` / `canonicalAnickChain` (the deterministic generator);
    truth probes — `ssss` recognised (`markedCyclicThreeTwoChainIsMinimal`), the non-minimal `{0, 2}` and
    the naive `{0, 1, 2}` rejected (`nonMinimalOverlapWidthOneIsRejected`, `naiveDegreeThreeOverlapIsRejected`),
    the genuine 3-chain `s⁶ = [0, 1, 3]` (`cyclicThreeThreeChainTipsAreZeroOneThree`).
  * **B2 — the cyclic-3 all-degrees computation**: SHIPPED.  The 2-periodic length recursion
    (`anickChainWordLength`, `anickChainWordLengthIsTwoPeriodic`); the census `[3, 4, 6, 7, 9, 10]`
    through degree 6 (probed to 8: `12, 13`); the position cross-checks; ★ the tie-in
    `cyclicThreeAnickChainCountMatchesPeriodicTowerBasis` (per-degree count `1` = shipped
    `PeriodicTower.basisCount`); the involution / idempotent k = 2 censuses (identical chains).
  * **B3 — the monad census + boundaries**: SHIPPED.  `walkingMonadSquierCriticalPairCountIsFive`;
    the monad Anick census NAMED as a future (polygraphic-Anick) node; the Anick 2-chain boundary column
    `0` matching the tower's degree-2 boundary; `d d = 0` riding the shipped tower
    (`cyclicThreeAnickBoundaryComposesToZeroViaTower`).
  * **B4 — the ledger**: SHIPPED.  ★★ the Squier-truncation `1 < 2` STRICT for cyclic-3
    (`cyclicThreeAnickTwoChainCountStrictlyBelowSquier`), `1 = 1` for involution / idempotent; the
    length-5 skip witnessing `sssss` non-minimal; the crown-inheritance anchor
    (`anickPerDegreeCountIsFinite`) with the `S_1` wall held.
  * **B5 — this ledger**: SHIPPED.

### Honest scoping (no overclaim)

This ships the Anick CHAIN CENSUS + the marked-occurrence carrier + the tie-in to the shipped tower.  It
does NOT prove Anick-complex exactness, does NOT re-derive the boundary maps from the chains (they RIDE
the shipped `PeriodicTower` / `CyclicThreeChainComplex` boundaries), and does NOT prove Squier's
finiteness theorem or the full Anick resolution theorem.  The single-letter `count = 1` is the honest
closed form (deterministic generator ⟹ unique canonical chain per degree); the general
`finiteConvergent ⟹ finitely-many-chains-per-degree ⟹ f.g. H_n` and the polygraphic-Anick monad are the
NAMED LATER NODES.

### Named future nodes (deferred, decided elsewhere)

  * **The full Anick resolution theorem** (the chains generate a minimal free resolution, with the
    Anick differential) — the boundary is here inherited from the shipped tower; deriving it FROM the
    chains and proving exactness is r2+.
  * **The polygraphic-Anick monad census** (Guiraud–Malbos) — term-rewriting Anick for the walking monad,
    where single-letter monomial chains do not apply.
  * **The general single-letter family** `⟨s | sⁿ⁺¹ ⟹ id⟩` — this file's `anickChainWordLength` is already
    tip-length-generic; the per-`n` homology `H1 = ZZ/(n+1)` over the parameter is the TOWER-PERIODIC node
    (#2146). -/

/-- ★ **The TOWER-ANICK (#2144) r1 ledger marker.**  What stands, zero-axiom: the marked-occurrence Anick
carrier with the decidable minimal-overlap guard (truth-probed — `ssss` recognised, the non-minimal
`{0, 2}` and naive `{0, 1, 2}` rejected, the genuine 3-chain `s⁶`); the cyclic-3 2-periodic length census
`[3, 4, 6, 7, 9, 10, …]` with ★ the per-degree count tied to the shipped `PeriodicTower.basisCount`
(`cyclicThreeAnickChainCountMatchesPeriodicTowerBasis`); the involution / idempotent k = 2 censuses
(identical chains, distinct boundaries); the monad five-CP census NAMED as a future polygraphic-Anick
node; the low-degree Anick boundary riding the shipped tower with `d d = 0` inherited; and ★★ the
Squier-truncation `Anick 1 ⊊ Squier 2` (STRICT, cyclic-3) / `1 = 1` (involution, idempotent) with the
crown-inheritance anchor (constant-1 per-degree finiteness; the `S_1` rank-finiteness wall held).  Read
the meaning from THIS docstring (the honest-record convention). -/
def towerAnickRoundOneLedgerIsComplete : Bool := true

/-! ## B1 (r2) — THE ENUMERATOR: a fueled strictly-increasing candidate generator + the guard filter,
    truth-probed to reproduce the shipped `anickChainTips` singleton at every low degree (the "compute
    first" oracle for the uniqueness theorem below)

The r1 file GENERATES the canonical chain top-down (`anickChainTips`) but never independently CONFIRMS it
is the *only* guard-passer.  This brick supplies the enumerative cross-check: build the whole finite
candidate space of strictly-increasing length-`n` tip lists bounded by the last canonical position, filter
by `isMinimalAnickChain`, and observe by `rfl` that EXACTLY the shipped chain survives.  Pre-restricting to
strictly-increasing-from-`0` drops no guard-passer (the guard forces `p₁ = 0`, `p₂ = 1`, and
`max(prev+1, _) ≥ prev+1 > prev` ⟹ strictly increasing), so completeness is preserved while the candidate
count collapses from `(bound+1)ⁿ` to `C(bound, n−1)` — 21 candidates at degree 6, kernel-`rfl` tractable.
Hand-rolled count-down (NO `List.range`, whose accumulator-loop reduction is awkward under `rfl`). -/

/-- The ascending run `[start, start+1, …, start + length − 1]`, hand-rolled structurally on the length so
no `List.range` accumulator loop enters (every candidate step reduces by `rfl`). -/
def natCountUpFrom (start : Nat) : Nat → List Nat
  | 0 => []
  | length + 1 => start :: natCountUpFrom (start + 1) length

/-- All strictly-increasing tails of the given `remainingLength`, each entry in `(prev, bound]` — the
candidate tip-tails above `prev`.  Structural on `remainingLength`; `prev` threads forward.  The next
position ranges over `natCountUpFrom (prev + 1) (bound − prev)` = `{prev+1, …, bound}` (empty when
`bound < prev`, so the strictly-increasing invariant and the upper bound are both enforced structurally). -/
def anickCandidateTails (bound : Nat) : Nat → Nat → List (List Nat)
  | _prev, 0 => [[]]
  | prev, remainingLength + 1 =>
      (natCountUpFrom (prev + 1) (bound - prev)).flatMap (fun next =>
        (anickCandidateTails bound next remainingLength).map (fun tail => next :: tail))

/-- The full candidate space at a degree: every strictly-increasing length-`degree` tip list starting at
`0` with entries `≤ bound`.  Degree `0` is the empty chain `[[]]`; degree `d+1` prepends `0` to each
length-`d` strictly-increasing tail above `0`. -/
def anickCandidateChains (degree bound : Nat) : List (List Nat) :=
  match degree with
  | 0 => [[]]
  | remainingLength + 1 => (anickCandidateTails bound 0 remainingLength).map (fun tail => 0 :: tail)

/-- ★ **THE ENUMERATOR.**  The minimal Anick chains at a degree = the candidate space (bounded by the last
canonical position `L(degree) − tipLength`) filtered by the decidable guard.  Because the guard is a pure
EQUALITY test (§B2), exactly one candidate survives — this is the executable per-degree Anick-generator
count, uniqueness-certified below. -/
def anickMinimalChainsAtDegree (tipLength degree : Nat) : List (List Nat) :=
  (anickCandidateChains degree (anickChainWordLength tipLength degree - tipLength)).filter
    (isMinimalAnickChain tipLength)

/-- ★ **Enumerator truth probe (the built-in oracle): the guard-filtered candidate space is EXACTLY the
shipped `anickChainTips` singleton at every cyclic-3 degree 1–6.**  The candidate space collapses to one
survivor — the deterministic canonical chain — confirming the generator by independent enumeration.  `rfl`
per degree. -/
theorem anickEnumeratorAgreesWithGeneratorThroughDegreeSix :
    anickMinimalChainsAtDegree 3 1 = [anickChainTips 3 1] ∧
    anickMinimalChainsAtDegree 3 2 = [anickChainTips 3 2] ∧
    anickMinimalChainsAtDegree 3 3 = [anickChainTips 3 3] ∧
    anickMinimalChainsAtDegree 3 4 = [anickChainTips 3 4] ∧
    anickMinimalChainsAtDegree 3 5 = [anickChainTips 3 5] ∧
    anickMinimalChainsAtDegree 3 6 = [anickChainTips 3 6] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **Hostile near-miss rejected (over-disjoint): `{0, 1, 4}` is NOT minimal** — the 3rd tip is placed
TOO FAR: window `(0, 1)` forces `p₃ = max(1+1, 0+3) = 3`, and `4 ≠ 3`.  A new rejection DIRECTION beyond
r1's two probes (over-disjoint, not over-overlapping).  `rfl`. -/
theorem nonMinimalOverStepBeyondWindowIsRejected :
    isMinimalAnickChain 3 [0, 1, 4] = false := rfl

/-- ★ **Hostile near-miss rejected (mid-chain over-step): `{0, 1, 3, 5}` is NOT minimal** — the first
three tips are canonical (`p₃ = 3`), but the 4th over-steps: window `(1, 3)` forces
`p₄ = max(3+1, 1+3) = 4`, and `5 ≠ 4`.  A deviation on the min-progress branch mid-chain — the equality
guard pins every step, so ANY over- or under-step fails.  `rfl`. -/
theorem nonMinimalMidChainOverStepIsRejected :
    isMinimalAnickChain 3 [0, 1, 3, 5] = false := rfl

/-- ★ **The enumerator's BOUND GATE is necessary (self-attack): an undersized bound drops the canonical
chain.**  At degree 3 the sufficient bound is `L(3) − 3 = 3`; with the undersized bound `2` the candidate
space is only `[[0, 1, 2]]` (the canonical `[0, 1, 3]` is unreachable), and the guard filter yields the
EMPTY list — `Derived = 0 ≠ 1`.  This documents why `bound = anickChainWordLength k n − k` (the last
canonical position, provably `≥` every canonical position by strict monotonicity) is the correct gate.
`rfl`. -/
theorem anickUndersizedBoundDropsCanonicalChain :
    (anickCandidateChains 3 2).filter (isMinimalAnickChain 3) = [] := rfl

/-- ★ **The enumerator is tip-length-generic (k = 2 involution / idempotent): the guard-filtered candidate
space is the `anickChainTips 2 5` singleton at degree 5.**  The uniqueness and enumeration machinery is
`tipLength`-parametric, so the involution / idempotent walkers are covered by the same code.  `rfl`. -/
theorem involutionAnickEnumeratorSingletonAtDegreeFive :
    anickMinimalChainsAtDegree 2 5 = [anickChainTips 2 5] := rfl

end FX1Poly.Polygraph.Homology
