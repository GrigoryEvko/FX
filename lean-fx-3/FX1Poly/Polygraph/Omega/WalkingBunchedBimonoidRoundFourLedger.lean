import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidNormalFormCensus

/-! # Polygraph/Omega/WalkingBunchedBimonoidRoundFourLedger — the WP-PROP r4 grand ledger (#2033, the 110-percent
grind: the hexagon + the star at the honest scope)

★ **The honest r4 scoreboard: what landed, every jam a NAMED node with its exact goal, every upstream wall
byte-intact.**  WP-PROP r4 advanced the additive-fragment matrix-PROP correspondence on four bricks:

  * **B1 THE HEXAGON** — the width-3 rows (Yang-Baxter + mu/delta wide-symmetry naturality) are matrix-respected
    (`rfl`) and ADDED additively over `BunchedBimonoidSoundRow` through the shipped `unionCellRel`, with the
    widened soundness `bunchedBimonoidMatrixSoundOverHexagon` and two completeness instances.  The r3 hexagon
    walls are retired NAME-ONLY at literal delivery.
  * **B2 THE PERM-LAYER** — `spiderOf` is adjudicated as spider-WITH-PERMUTATION-MIDDLE (recon self-attack #3):
    the three-stage NF form, the permutation-word NF (swap = `sigma`, reversal = the Yang-Baxter word,
    round-tripped), and the perm-layer irreducibility (unreachable by block placement).
  * **B3 THE NF INDUCTION + THE STAR** — the per-`CellExpr`-ctor census, and the #2033 star NAMED
    (`bunchedBimonoidStarStatement`) at its honest scope `StrictAxiomRel union SoundRow union HexagonRow`, NOT
    proven (r5, no flip).
  * **B4 THE LEDGER** — this file.

## The remaining nodes (each a NAMED jam with its exact goal)

  * **Node A residual (1) — general `matMul` associativity.**  `matMul (matMul A B) C = matMul A (matMul B C)`
    for well-formed composable matrices, the 3-factor finite-sum Fubini with the `List.range` double-sum swap +
    distributivity (`Nat.add_mul` leaks `propext`, so a hand-rolled distributivity is needed).  Only the concrete
    `rfl` probes `bunchedBimonoidMatMulAssocConcrete{TwoByTwo,NonSquare}` (r2) are shipped.
  * **Node A residual (2) — general-`n` identity-matrix unit laws.**  `matMul M (identityMat M.cols) = M`
    (and left) for an ARBITRARY well-formed `M`, requiring the `List (List Nat)` matrix reconstruction the
    block-exchange deliberately dodged.  Only the `1 x 1` singletons `bunchedBimonoidIdentity{Left,Right}
    UnitSingleton` (r3) are shipped.
  * **Node C — the general routing perm-stage.**  `spiderOf : Mat -> CellExpr` reading an ARBITRARY permutation
    off `M`'s row-major-to-column-sum transpose — the riskiest encoding member.  The hexagon rows supply the
    permutation GENERATORS; the transpose that reads the specific permutation is deferred.
  * **The star (the retraction) — r5.**  `bunchedBimonoidStarStatement` (equal matrix ⟹ convertible over the
    widened congruence, for ALL 2-cells) is the NF induction; it needs Node A + Node C.

## Every upstream `= false` marker is byte-intact (additive-only)

`fxBunchedBimonoid_matrixHexagonReached`, `...starVcompCoherenceHexagonWall`, `...starStrictLawExtensionWall`,
`...matrixStrictLawExtensionReached`, `...fullIsolationNeedsStrictLawFubiniKit`, `...spiderGeneralRoutingReached`,
`...spiderGeneralRoundTripBlockExchangeWall`, `...spiderNormalFormStarNamedRThree`,
`...propGeneralCompletenessStarReached`, `...matrixCompletenessIsSpiderNormalFormWall`,
`...spiderCompletenessTargetsSoundSubTheory` — all keep their name and `= false` value; r4 retires them NAME-ONLY
through fresh markers only where the content is LITERALLY delivered (the hexagon), and NARROWS them where a
component landed (Node A block-multiplicativity + hexagon).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The r4 deliverables (bricks B1-B3, cross-referenced) -/

/-- ★★★ **LEDGER (B1) — the hexagon is delivered.**  `= true` records that the width-3 hexagon rows
(`BunchedBimonoidHexagonRow` — Yang-Baxter + mu/delta wide-symmetry naturality) are matrix-respected and added
additively over `BunchedBimonoidSoundRow`, with `bunchedBimonoidMatrixSoundOverHexagon` (widened soundness) and
`bunchedBimonoid{YangBaxter,MuNaturality}CompletenessInstance` (two completeness instances).  The r3 hexagon
wall's width-3 content is literally shipped; `fxBunchedBimonoid_hexagonWallRetiredNameOnly` retires it by name. -/
def fxBunchedBimonoid_r4HexagonDelivered : Bool := true

/-- ★★★ **LEDGER (B2) — the perm-layer is delivered.**  `= true` records the spider-with-perm-middle
adjudication: the three-stage NF form `bunchedBimonoidSpiderStaged`, the permutation-word NF
(`bunchedBimonoidSpiderPermTwo` = `sigma`, `bunchedBimonoidSpiderPermReversalThree` = the Yang-Baxter word, both
round-tripped), and the perm-layer irreducibility (`bunchedBimonoidPermLayerIsLoadBearing` +
`...ReversalNotIdentity`).  The honest `spiderOf` reach is block-diagonal (r3) + permutation words (r4). -/
def fxBunchedBimonoid_r4PermLayerDelivered : Bool := true

/-- ★★★ **LEDGER (B3) — the star is NAMED at its honest scope.**  `= true` records that the #2033 star
(`bunchedBimonoidStarStatement`) is stated over the widened congruence `StrictAxiomRel union SoundRow union
HexagonRow` (`bunchedBimonoidStarCongruenceScope`), with the three row-family embeddings, and the per-ctor NF
census (`fxBunchedBimonoid_nfInductionCensusShipped`).  The star scope widens visibly — the recon's single most
important honesty constraint. -/
def fxBunchedBimonoid_r4StarScopeNamed : Bool := true

/-! ## The remaining nodes — each a NAMED jam with its exact goal -/

/-- ★ **NODE A residual (1) — general `matMul` associativity is NOT shipped.**  `= false` records the exact goal:
`bunchedBimonoidMatMul (bunchedBimonoidMatMul A B) C = bunchedBimonoidMatMul A (bunchedBimonoidMatMul B C)` for
well-formed composable `A, B, C` — the 3-factor finite-sum Fubini (the `List.range` double-sum swap +
distributivity, with a hand-rolled `Nat.add_mul` because Init's leaks `propext`).  Only the concrete `rfl` probes
`bunchedBimonoidMatMulAssocConcrete{TwoByTwo,NonSquare}` (r2) are shipped; the general lemma is genuine 3-factor
Fubini work.  This is component (1) of `fxBunchedBimonoid_matrixStrictLawExtensionReached` (byte-intact). -/
def fxBunchedBimonoid_r4RemainingNodeMatMulAssoc : Bool := false

/-- ★ **NODE A residual (2) — general-`n` identity-matrix unit laws are NOT shipped.**  `= false` records the
exact goal: `bunchedBimonoidMatMul M (bunchedBimonoidIdentityMat M.cols) = M` (and the left unit) for an
ARBITRARY well-formed `M`, needing the `List (List Nat)` matrix reconstruction (`(range M.rows).map (range
M.cols).map (matEntryAt M) = M.entries`) the block-exchange DELIBERATELY dodged by keeping every matrix in
`List.range` / `List.replicate` normal form.  Only the `1 x 1` singleton units
`bunchedBimonoidIdentity{Left,Right}UnitSingleton` (r3) are shipped.  Component (2) of
`fxBunchedBimonoid_matrixStrictLawExtensionReached` (byte-intact). -/
def fxBunchedBimonoid_r4RemainingNodeGeneralUnits : Bool := false

/-- ★ **NODE C — the general routing perm-stage is NOT shipped.**  `= false` records the exact goal: a general
`spiderOf : BunchedBimonoidMat -> CellExpr bunchedBimonoidOmegaComputad 2` whose perm-stage reads an ARBITRARY
permutation off `M`'s row-major-to-column-sum TRANSPOSE (a `List (List Nat)` transpose helper, the riskiest
encoding member).  The hexagon rows (B1) supply the permutation-word GENERATORS and the block-exchange (r3)
supplies the block placement, but the transpose that reads the specific permutation is deferred.  Same wall as
`fxBunchedBimonoid_spiderGeneralRoutingReached` (byte-intact). -/
def fxBunchedBimonoid_r4RemainingNodeGeneralRouting : Bool := false

/-- ★ **THE STAR (the retraction) — r5.**  `= false` records that `bunchedBimonoidStarStatement` (equal `Mat(N)`
matrix ⟹ convertible over the widened congruence, for ALL 2-cells) — the NF induction / diagram-to-matrix
retraction, the #2033 star — is NOT proven in r4.  It needs Node A (the strict-law matrix-soundness extension)
and Node C (the general routing).  The upstream star markers `fxBunchedBimonoid_spiderNormalFormStarNamedRThree`
/ `...propGeneralCompletenessStarReached` stay `= false` (byte-intact); no fake flip. -/
def fxBunchedBimonoid_r4StarIsRFive : Bool := false

/-! ## The additive-only invariant + the grand ledger -/

/-- ★★ **EVERY UPSTREAM `= false` MARKER IS BYTE-INTACT (additive-only).**  `= true` records that r4 modified NO
r1/r2/r3 Omega source: the hexagon / perm-layer / NF-census content is delivered in fresh files
(`WalkingBunchedBimonoid{Hexagon,PermStage,NormalFormCensus,RoundFourLedger}`), and every upstream wall marker
(`fxBunchedBimonoid_matrixHexagonReached`, `...starVcompCoherenceHexagonWall`, `...starStrictLawExtensionWall`,
`...matrixStrictLawExtensionReached`, `...fullIsolationNeedsStrictLawFubiniKit`, `...spiderGeneralRoutingReached`,
`...spiderGeneralRoundTripBlockExchangeWall`, `...spiderNormalFormStarNamedRThree`,
`...propGeneralCompletenessStarReached`) keeps its name and `= false` value.  r4 retires walls NAME-ONLY through
fresh markers ONLY at literal delivery (the hexagon) and NARROWS them where a component landed (Node A
block-multiplicativity + the hexagon braiding). -/
def fxBunchedBimonoid_r4UpstreamWallsByteIntact : Bool := true

/-- ★★★ **ESTABLISHED (B4) — the WP-PROP r4 grand ledger (the honest scoreboard).**  `= true` records the
complete r4 advance: B1 the hexagon delivered (`fxBunchedBimonoid_r4HexagonDelivered`); B2 the perm-layer
delivered (`fxBunchedBimonoid_r4PermLayerDelivered`); B3 the star NAMED at its honest scope `StrictAxiomRel union
SoundRow union HexagonRow` (`fxBunchedBimonoid_r4StarScopeNamed`), NOT proven (`fxBunchedBimonoid_r4StarIsRFive =
false`); and the remaining nodes each NAMED at its exact goal — Node A (1) general `matMul` associativity + (2)
general-`n` identity units + Node C the general routing transpose (all `= false`, exact goals stated).  Every
upstream `= false` marker byte-intact (`fxBunchedBimonoid_r4UpstreamWallsByteIntact`); additive-only.  The star
(the retraction) is r5. -/
def fxBunchedBimonoid_roundFourGrandLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
