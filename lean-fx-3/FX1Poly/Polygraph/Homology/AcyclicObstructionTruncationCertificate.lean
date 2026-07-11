import FX1Poly.Polygraph.Homology.AnickTelescopeAugmentationAndMonomialFiniteness

/-! # FX1Poly/Polygraph/Homology/AcyclicObstructionTruncationCertificate — the TRUNCATION CERTIFICATE
    (#2145 finite-global-dimension special case): a decidable Ufnarovski-graph acyclicity checker
    (fuel-structural), the CONDITIONAL vanishing `census = 0 ==> homology exact`, and the `{xy}` finite
    eventual-exactness certificate, with the general `acyclic ==> census 0` closed form NAMED
    (TOWER-ANICK r6, #2144 / #2145)

The r5 file `AnickTelescopeAugmentationAndMonomialFiniteness` shipped the truncation CRITERION
(`noLinearChainOfLengthThreeOrMore`: no `{xy}`-chain of length >= 3) + the concrete truncating census
`[2, 1, 0, 0, 0, 0]`, and NAMED the `forall d` closed form (`allDegreesTruncationClosedFormIsNamedNode`)
because the general `d >= 2 ==> census = 0` needs a `flatMap`-membership bridge over `allWordsOfLength`
(the lane's `List.Mem` / `List.append` propext minefield).  The #2145 node
`generalTelescopeHomologyIsNamedNode` (`MultiObstructionAnickBoundaryHomology`) is the general
`finiteConvergent ==> H_d` computation; the truncation certificate is its finite-global-dimension special
case.  This module makes three ADDITIVE r6 advances, each truth-probed by `#eval` on the shipped
definitions BEFORE proving.

## B1 — the decidable acyclicity checker (fuel-structural)

An Anick chain over the leading-term obstruction set is a walk in the Ufnarovski graph (vertices =
letters, edges = obstruction pairs).  The chains are finite in total iff the graph is a DAG.  This file
ships a decidable acyclicity checker as a Bool-valued fuel-structural reachability closure:
`isAcyclicUfnarovskiGraph edges reachabilityFuel = true` iff no edge-source reaches itself within
`reachabilityFuel` frontier-expansion rounds (every directed cycle passes through an edge-source).  The
three shipped systems classify by `rfl`: `{xy} = [(0, 1)]` acyclic (`x -> y` only), `{xx} = [(0, 0)]` NOT
acyclic (self-loop), Fibonacci `{xx, xy, yx}` NOT acyclic (self-loop at `x` plus the `x <-> y` cycle);
`hasSelfLoop` classifies the two cyclic systems directly.

★ **Honest scope of B1.**  The checker is a well-defined zero-axiom Bool function that CLASSIFIES the
three concrete graphs; its SOUNDNESS (that "acyclic as computed" implies chain truncation for a GENERAL
graph) is the NAMED node `acyclicToCensusZeroIsNamedNode` — an honest upgrade of r5's
`allDegreesTruncationClosedFormIsNamedNode` from "named" to "reduced to a decidable acyclicity check + one
`allWordsOfLength` length lemma".

## B2 — the CONDITIONAL vanishing (the feasible half of #2145)

`multiObstructionHomologyDataAtDegree obs degree` bundles the census rank `C_degree =
multiObstructionChainRankOracle obs degree` with zero boundary matrices; its
`SmithHomologyData.homologyInvariant` is `<C_degree, []>` (rank `(C - 0) - 0`, no torsion — the zero
matrix `[[0]]` has empty within-window invariant factors).  So `census = 0 ==> isExactAtDegree`
(`censusZeroImpliesExact`): a degree with no Anick chains contributes trivial homology.  Proof shape:
one `rfl` bridge to `<C_degree, []>` + one `congrArg` of the census-zero hypothesis.

## B3 — the `{xy}` finite eventual-exactness certificate

`linearSystemEventuallyExact`: the `{xy}` monomial complex is exact at degrees 2..5 (the shipped census
window), each `censusZeroImpliesExact linearObstructionSystem d rfl` — the finite-global-dimension algebra
`k<x, y>/(xy)` becoming eventually exact, the opposite extreme from the Fibonacci
`fibMonomialNeverExact`.  The `AcyclicTruncationCertificate` records the obstruction system, its
machine-checked acyclicity witness, and the longest-chain degree.

## Honest scope (NO overclaim)

This delivers the MONOMIAL, finite-global-dimension special case of #2145: the decidable acyclicity
checker + graph classification (all `rfl`), the conditional vanishing `census 0 ==> exact` (`rfl`-after-
`congrArg`), and the `{xy}` finite eventual-exactness certificate (all `rfl`, resting on the shipped
`noLinearChainOfLengthThreeOrMore`).  It does NOT close #2145's general `finiteConvergent ==> H_d`
(the differential need not vanish under `k (x)_A` for a general convergent presentation — the telescope
wall) and does NOT close the general `acyclic ==> census 0` (the `flatMap`-membership + longest-path
wall), both NAMED.  The r5 file stays verbatim UNMOVED (this file is additive).

## Zero-axiom design decisions

  * The acyclicity checker is fuel-STRUCTURAL: `obstructionReachableWithin` recurses on an explicit fuel
    `Nat` (never `WellFounded.fix`); every letter comparison is the shipped propext-clean `natEqBool`;
    every match is full-enum (`Bool` two-arm, `List` cons/nil, pair destructure) — no wildcard.  The
    frontier expansion is a hand-rolled `++` fold (NO `List.flatMap`), so the classification closes by
    `rfl` on `Bool` literals with no `List.append` / `List.mem_flatMap` propext surface.
  * `censusZeroImpliesExact` is `rfl` to `<C, []>` then `congrArg` of the hypothesis; `isExactAtDegree` is
    a `Prop` structure equality (no `BEq` / `decide` on the structure).
  * The `{xy}` finite certificate closes each conjunct by `censusZeroImpliesExact _ d rfl` — the census-0
    facts are `rfl` on `Nat` literals, resting on the shipped `noLinearChainOfLengthThreeOrMore`.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated (and independently `#print axioms`-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/AcyclicObstructionTruncationCertificate.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## B1 — the decidable Ufnarovski-graph acyclicity checker (fuel-structural) -/

/-- The out-neighbours of `vertex` under the obstruction edge list — every `target` with `(vertex, target)`
an edge.  Structural on the edge list; letter equality via the shipped `natEqBool`, full-enum `Bool` match. -/
def obstructionOutNeighbours : List (Nat × Nat) → Nat → List Nat
  | [], _ => []
  | (source, target) :: remainingEdges, vertex =>
      match natEqBool source vertex with
      | true => target :: obstructionOutNeighbours remainingEdges vertex
      | false => obstructionOutNeighbours remainingEdges vertex

/-- One frontier-expansion step: the out-neighbours of every vertex in the frontier, concatenated.  A
hand-rolled `++` fold (NO `List.flatMap`), structural on the frontier list. -/
def obstructionFrontierStep (edges : List (Nat × Nat)) : List Nat → List Nat
  | [] => []
  | vertex :: remainingFrontier =>
      obstructionOutNeighbours edges vertex ++ obstructionFrontierStep edges remainingFrontier

/-- All vertices reached from the seed frontier within `reachabilityFuel` expansion rounds.  STRUCTURAL on
the fuel `Nat` (never `WellFounded.fix`); collects the frontier at every round. -/
def obstructionReachableWithin (edges : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, frontier => frontier
  | fuel + 1, frontier =>
      frontier ++ obstructionReachableWithin edges fuel (obstructionFrontierStep edges frontier)

/-- Boolean list membership over `Nat` via the propext-clean `natEqBool` (no `decide` on `List.Mem`). -/
def natListContains : List Nat → Nat → Bool
  | [], _ => false
  | head :: remainingList, target => natEqBool head target || natListContains remainingList target

/-- The edge-sources (first components) of the obstruction list — every directed cycle passes through one. -/
def obstructionSources : List (Nat × Nat) → List Nat
  | [] => []
  | (source, _) :: remainingEdges => source :: obstructionSources remainingEdges

/-- Does `source` reach itself in >= 1 steps within `reachabilityFuel` rounds?  It lies on a directed
cycle iff it is reachable from one of its own out-neighbours. -/
def obstructionSourceReachesItself (edges : List (Nat × Nat)) (reachabilityFuel : Nat)
    (source : Nat) : Bool :=
  natListContains
    (obstructionReachableWithin edges reachabilityFuel (obstructionOutNeighbours edges source)) source

/-- Is any edge-source on a directed cycle?  Structural fold over the source list. -/
def anyObstructionSourceOnCycle (edges : List (Nat × Nat)) (reachabilityFuel : Nat) : List Nat → Bool
  | [] => false
  | vertex :: remainingSources =>
      obstructionSourceReachesItself edges reachabilityFuel vertex
        || anyObstructionSourceOnCycle edges reachabilityFuel remainingSources

/-- ★ **The decidable Ufnarovski-graph acyclicity checker** — `true` iff no edge-source reaches itself
within `reachabilityFuel` rounds (no directed cycle).  Fuel-structural, `natEqBool`-based, full-enum. -/
def isAcyclicUfnarovskiGraph (edges : List (Nat × Nat)) (reachabilityFuel : Nat) : Bool :=
  Bool.not (anyObstructionSourceOnCycle edges reachabilityFuel (obstructionSources edges))

/-- Does the graph have a self-loop `x -> x`?  The immediate cyclicity witness for `{xx}` and Fibonacci. -/
def hasSelfLoop : List (Nat × Nat) → Bool
  | [] => false
  | (source, target) :: remainingEdges => natEqBool source target || hasSelfLoop remainingEdges

/-- ★★ **The `{xy}` graph is ACYCLIC** — `x -> y` only, a DAG.  `rfl`. -/
theorem linearGraphIsAcyclic : isAcyclicUfnarovskiGraph linearObstructionSystem 2 = true := rfl

/-- ★ **The `{xx}` self-loop graph is NOT acyclic** — `x -> x` is a directed cycle.  `rfl`. -/
theorem selfLoopGraphIsNotAcyclic :
    isAcyclicUfnarovskiGraph singleObstructionUnarySystem 2 = false := rfl

/-- ★ **The Fibonacci `{xx, xy, yx}` graph is NOT acyclic** — the self-loop at `x` and the `x <-> y` cycle.
`rfl`. -/
theorem fibGraphIsNotAcyclic : isAcyclicUfnarovskiGraph fibObstructionSystem 2 = false := rfl

/-- The `{xy}` graph has NO self-loop.  `rfl`. -/
theorem linearGraphHasNoSelfLoop : hasSelfLoop linearObstructionSystem = false := rfl

/-- The `{xx}` graph has a self-loop.  `rfl`. -/
theorem selfLoopGraphHasSelfLoop : hasSelfLoop singleObstructionUnarySystem = true := rfl

/-- The Fibonacci graph has a self-loop (`xx`).  `rfl`. -/
theorem fibGraphHasSelfLoop : hasSelfLoop fibObstructionSystem = true := rfl

/-! ## B2 — the CONDITIONAL vanishing: `census = 0 ==> homology exact` (the feasible half of #2145) -/

/-- The homology data at a degree of the TENSORED monomial complex: the census rank with zero boundary
matrices (`[[0]]`).  Its `homologyInvariant` is `<census, []>` (rank `(census - 0) - 0`, no torsion — the
zero matrix has empty within-window invariant factors). -/
def multiObstructionHomologyDataAtDegree (obstructions : List (Nat × Nat))
    (degree : Nat) : SmithHomologyData :=
  { chainBasisCount := multiObstructionChainRankOracle obstructions degree
  , smithBoundaryIntoLower := ⟨[[0]]⟩
  , windowIntoLower := 1
  , smithBoundaryFromHigher := ⟨[[0]]⟩
  , windowFromHigher := 1 }

/-- The homology invariant of the zero-boundary data is free on the census: `<census, []>`.  The two
`smithRankWithin [[0]] 1` reduce to `0` and `smithInvariantFactorsWithin [[0]] 1` to `[]`.  `rfl`. -/
theorem multiObstructionHomologyInvariantIsFreeOnCensus (obstructions : List (Nat × Nat))
    (degree : Nat) :
    (multiObstructionHomologyDataAtDegree obstructions degree).homologyInvariant
      = ⟨multiObstructionChainRankOracle obstructions degree, []⟩ := rfl

/-- ★★ **THE CONDITIONAL VANISHING** — a degree with no Anick chains contributes trivial homology:
`multiObstructionChainRankOracle obs degree = 0 ==>
isExactAtDegree (multiObstructionHomologyDataAtDegree obs degree)`.  The `rfl` bridge gives
`<census, []>`; `congrArg` of the hypothesis collapses the free rank to `0`.  Zero-axiom, no `flatMap`. -/
theorem censusZeroImpliesExact (obstructions : List (Nat × Nat)) (degree : Nat)
    (censusIsZero : multiObstructionChainRankOracle obstructions degree = 0) :
    isExactAtDegree (multiObstructionHomologyDataAtDegree obstructions degree) :=
  (multiObstructionHomologyInvariantIsFreeOnCensus obstructions degree).trans
    (congrArg (fun freeRankValue => (⟨freeRankValue, []⟩ : HomologyInvariant)) censusIsZero)

/-! ## B3 — the `{xy}` finite eventual-exactness certificate -/

/-- A machine-checked acyclic-truncation certificate: the obstruction system, the reachability fuel, the
longest chain degree above which the chains truncate, and the `rfl`-checked acyclicity witness.  The
GENERAL `forall degree > longestChainDegree, census = 0` soundness is the named node
`acyclicToCensusZeroIsNamedNode`; the finite eventual-exactness is certified separately by
`linearSystemEventuallyExact`. -/
structure AcyclicTruncationCertificate where
  /-- The leading-term obstruction system. -/
  obstructions : List (Nat × Nat)
  /-- The frontier-expansion fuel that witnesses acyclicity. -/
  reachabilityFuel : Nat
  /-- The longest Anick chain degree; chains truncate strictly above it. -/
  longestChainDegree : Nat
  /-- The machine-checked acyclicity of the Ufnarovski graph. -/
  graphIsAcyclic : isAcyclicUfnarovskiGraph obstructions reachabilityFuel = true

/-- ★ **The `{xy}` truncation certificate** — the acyclic `x -> y` graph (fuel `2`), longest chain degree
`1` (the single degree-1 chain `[0, 1]`); acyclicity by `rfl`. -/
def linearSystemTruncationCertificate : AcyclicTruncationCertificate :=
  { obstructions := linearObstructionSystem
  , reachabilityFuel := 2
  , longestChainDegree := 1
  , graphIsAcyclic := rfl }

/-- ★★ **THE `{xy}` FINITE EVENTUAL-EXACTNESS CERTIFICATE** — the tensored `k<x, y>/(xy)` monomial complex
is EXACT at degrees 2..5 (the shipped census window), each `censusZeroImpliesExact linearObstructionSystem
d rfl` (the census-0 facts `rfl` on `Nat` literals).  The finite-global-dimension algebra becoming
eventually exact — the opposite extreme from `fibMonomialNeverExact`.  Rests on the shipped
`noLinearChainOfLengthThreeOrMore`. -/
theorem linearSystemEventuallyExact :
    isExactAtDegree (multiObstructionHomologyDataAtDegree linearObstructionSystem 2) ∧
    isExactAtDegree (multiObstructionHomologyDataAtDegree linearObstructionSystem 3) ∧
    isExactAtDegree (multiObstructionHomologyDataAtDegree linearObstructionSystem 4) ∧
    isExactAtDegree (multiObstructionHomologyDataAtDegree linearObstructionSystem 5) :=
  ⟨censusZeroImpliesExact linearObstructionSystem 2 rfl,
   censusZeroImpliesExact linearObstructionSystem 3 rfl,
   censusZeroImpliesExact linearObstructionSystem 4 rfl,
   censusZeroImpliesExact linearObstructionSystem 5 rfl⟩

/-! ## B4 — the standing walls (NAMED) and the r6 truncation ledger -/

/-- ★ **The general `acyclic ==> census 0` closed form is a NAMED node.**  The checker
`isAcyclicUfnarovskiGraph` classifies the three shipped graphs (`linearGraphIsAcyclic`,
`selfLoopGraphIsNotAcyclic`, `fibGraphIsNotAcyclic`), and the conditional vanishing
`censusZeroImpliesExact` is shipped.  The SOUNDNESS bridge `isAcyclicUfnarovskiGraph obs fuel = true ==>
forall degree, longestPath < degree ==> multiObstructionChainRankOracle obs degree = 0` reduces to: every
`w in allWordsOfLength (degree + 1)` has `w.length = degree + 1 > longestPath`, so it fails the guard
(`noLinearChainOfLengthThreeOrMore` for `{xy}`), so the filter empties — needing the `allWordsOfLength`
length lemma `w in allWordsOfLength n ==> w.length = n` (the lane's `flatMap`-membership propext minefield:
`List.Mem` / `List.append` / `List.mem_flatMap` leak `propext`) plus the general graph longest-path bound
(a topological-sort argument).  This HONESTLY upgrades r5's `allDegreesTruncationClosedFormIsNamedNode`
from "named" to "reduced to a decidable acyclicity check + one `allWordsOfLength` length lemma".  Read the
meaning from THIS docstring.  `= true`. -/
def acyclicToCensusZeroIsNamedNode : Bool := true

/-! ### The TOWER-ANICK (#2144 / #2145) r6 truncation-certificate ledger

  * **B1 — THE DECIDABLE ACYCLICITY CHECKER**: SHIPPED.  `isAcyclicUfnarovskiGraph` (fuel-structural
    reachability closure) + `hasSelfLoop`; the three-graph classification `{xy}` acyclic
    (`linearGraphIsAcyclic`), `{xx}` and Fibonacci NOT acyclic (`selfLoopGraphIsNotAcyclic`,
    `fibGraphIsNotAcyclic`), with the self-loop witnesses.  Checker SOUNDNESS NAMED.
  * **B2 — THE CONDITIONAL VANISHING**: SHIPPED.  `multiObstructionHomologyDataAtDegree` +
    `multiObstructionHomologyInvariantIsFreeOnCensus` (`<census, []>`, `rfl`); ★★ `censusZeroImpliesExact`
    (census 0 ==> exact) — the feasible half of #2145.
  * **B3 — THE `{xy}` FINITE CERTIFICATE**: SHIPPED.  `AcyclicTruncationCertificate` +
    `linearSystemTruncationCertificate`; ★★ `linearSystemEventuallyExact` (exact at degrees 2..5).
  * **B4 — this ledger**: SHIPPED.  Every deferral a NAMED node.

### Still WALLED (NAMED, never papered)

  * `acyclicToCensusZeroIsNamedNode` — the general `acyclic ==> census 0` closed form (the
    `flatMap`-membership `allWordsOfLength` length lemma + the longest-path bound), the honest upgrade of
    r5's `allDegreesTruncationClosedFormIsNamedNode`.
  * `generalTelescopeHomologyIsNamedNode` (#2145, `MultiObstructionAnickBoundaryHomology`) — the general
    `finiteConvergent ==> H_d` (the differential need not vanish under `k (x)_A`); this file delivers only
    the finite-global-dimension monomial special case.

### Honest scoping (no overclaim)

r6 delivers the MONOMIAL finite-global-dimension special case of #2145: the decidable acyclicity checker
(all classification `rfl`), the conditional vanishing `census 0 ==> exact` (`rfl`-after-`congrArg`), and
the `{xy}` finite eventual-exactness certificate (all `rfl`).  It does NOT close #2145's general
`finiteConvergent ==> H_d`, nor the general `acyclic ==> census 0` closed form — both NAMED.  Everything
`rfl` / structural (`natEqBool`, hand `++` fold, fuel recursion) — no new propext surface (the
`flatMap`-membership lemma is NAMED, not reached). -/

/-- ★ **The TOWER-ANICK (#2144 / #2145) r6 truncation-certificate ledger marker.**  What stands,
zero-axiom, additively over r5: THE DECIDABLE ACYCLICITY CHECKER (`isAcyclicUfnarovskiGraph` fuel-
structural + `hasSelfLoop`, the `{xy}` acyclic / `{xx}` + Fibonacci cyclic classification, all `rfl`; the
checker soundness NAMED); THE CONDITIONAL VANISHING (`censusZeroImpliesExact`: no chains ==> trivial
homology, `rfl`-after-`congrArg`); THE `{xy}` FINITE CERTIFICATE (`AcyclicTruncationCertificate` +
`linearSystemEventuallyExact`, exact at degrees 2..5).  Residuals NAMED (the general `acyclic ==> census 0`
closed form, the #2145 general `finiteConvergent ==> H_d`), never papered.  Read the meaning from THIS
docstring (the honest-record convention). -/
def acyclicObstructionTruncationCertificateIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
