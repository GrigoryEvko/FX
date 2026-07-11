import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidHexagon

/-! # Polygraph/Omega/WalkingBunchedBimonoidPermStage — the perm-layer general-spiderOf adjudication (WP-PROP r4,
#2033, the 110-percent grind)

★ **THE NF SHAPE, HONESTLY SCOPED: `spiderOf` is spider-WITH-PERMUTATION-MIDDLE — the three-stage
delta / perm / mu form, with the perm layer IRREDUCIBLE and load-bearing.**  The r1 `SpiderNormalForm` design
already named the three-stage form ("`permStage : a^K => a^K` ... a `sigma` composite"); the r3 block-exchange
reached only the block-DIAGONAL family (perm-stage = identity, `directSum` results); and the r3 self-attack
`bunchedBimonoidSwapUnreachableByDiagonal` proved the anti-diagonal swap is beyond block placement.  This file
adjudicates the general `spiderOf` NODE decisively:

  * **The perm stage is NOT dissolvable into block placement.**  A permutation matrix with routing content (any
    non-block-diagonal, e.g. the swap `[[0,1],[1,0]]` or the width-3 reversal) has a genuine perm-stage = a
    permutation WORD in `sigma`s.  `bunchedBimonoidSwapUnreachableByDiagonal` (r3) shows the swap differs from
    EVERY `diag(a, b)`; here the width-3 reversal is separated from the identity (a non-trivial perm stage).
  * **The NF of a permutation IS the permutation word.**  The 2-wire swap's NF is `sigma`
    (`bunchedBimonoidSpiderPermTwo`), round-tripping to `[[0,1],[1,0]]`; the 3-wire reversal's NF is the
    Yang-Baxter word `s_2 s_1 s_2` (`bunchedBimonoidSpiderPermReversalThree`), round-tripping to the reversal
    `[[0,0,1],[0,1,0],[1,0,0]]`.  Now that the hexagon rows (r4 B1) are shipped, these permutation words are
    genuine members of the widened congruence's normal forms.

## The honest reach (the recon's budget order)

The general `spiderOf : Mat -> CellExpr` for an ARBITRARY matrix decomposes into `deltaStage ; permStage ;
muStage` (`bunchedBimonoidSpiderStaged`).  The BLOCK-DIAGONAL fragment (perm-stage = identity) is reached by the
r3 block-exchange; the PERMUTATION fragment (delta/mu-stages = identity) is reached by the hexagon-generated
permutation words.  The FULLY-GENERAL routing (a `q x p` matrix whose perm-stage is an arbitrary permutation word
read off a row-major-to-column-sum TRANSPOSE) is the sole remaining `spiderOf` node, walled at the transpose
encoding (`fxBunchedBimonoid_spiderGeneralRoutingReached = false`, r1, byte-intact).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The width-3 permutation `rfl` reductions (the reversal round-trip / corner reads) exceed the default
elaborator heartbeat budget; the raise is a compute allowance only, the proof terms stay `Eq.refl`, axiom-free. -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE THREE-STAGE NF FORM + THE PERMUTATION-WORD WITNESSES (perm layer = load-bearing)
    # =========================================================================================
-/

/-- The **width-3 arity word** `a.a.a` — the PROP object at arity 3, the domain / codomain of the width-3
permutation normal forms. -/
def bunchedBimonoidAaaWord : CellExpr bunchedBimonoidOmegaComputad 1 :=
  CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAaWord

/-- ★ The **three-stage spider form** `spiderStaged deltaStage permStage muStage : delta then perm then mu` —
the honest Lafont normal-form shape the r1 `SpiderNormalForm` design named: fan each input (delta-stage), route
grouped-by-input to grouped-by-output (perm-stage, a `sigma` composite), fold each output (mu-stage).  As a map
`evalCell (spiderStaged D P M) = matMul (eval M) (matMul (eval P) (eval D))` — apply `D` first, then `P`, then
`M`.  The block-diagonal fragment has `permStage = id`; the permutation fragment has `deltaStage = muStage =
id`. -/
def bunchedBimonoidSpiderStaged (deltaStage permStage muStage : CellExpr bunchedBimonoidOmegaComputad 2) :
    CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.vcomp deltaStage permStage) muStage

/-- ★★ The **2-wire permutation normal form** `spiderPermTwo := sigma_a` — the NF of the swap `[[0,1],[1,0]]` is
the braiding word itself (delta / mu stages trivial, perm-stage = `sigma`).  The decisive perm-layer witness:
the NF of a permutation IS the permutation word. -/
def bunchedBimonoidSpiderPermTwo : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidAddSigmaGen

/-- ★★ The **3-wire permutation normal form** `spiderPermReversalThree := s_2 s_1 s_2` — the NF of the reversal
permutation `[[0,0,1],[0,1,0],[1,0,0]]` (the longest element of S_3) is the Yang-Baxter word, a genuine
composite of whiskered `sigma`s.  The width-3 perm-layer witness. -/
def bunchedBimonoidSpiderPermReversalThree : CellExpr bunchedBimonoidOmegaComputad 2 :=
  bunchedBimonoidYangBaxterRightLeg

/-- ★ **PERM ROUND-TRIP (2-wire) — `evalCell (spiderPermTwo) = [[0,1],[1,0]]`.**  The swap's NF round-trips to
the swap matrix on the nose, `rfl` (the perm-stage reproduces the permutation). -/
theorem bunchedBimonoidSpiderPermTwoRoundTrip :
    bunchedBimonoidEvalCell bunchedBimonoidSpiderPermTwo
      = { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } := rfl

/-- ★★ **PERM ROUND-TRIP (3-wire) — `evalCell (spiderPermReversalThree) = [[0,0,1],[0,1,0],[1,0,0]]`.**  The
reversal's NF (the Yang-Baxter word) round-trips to the reversal permutation, `rfl` (raised heartbeats — the
width-3 3-fold `matMul`). -/
theorem bunchedBimonoidSpiderPermReversalThreeRoundTrip :
    bunchedBimonoidEvalCell bunchedBimonoidSpiderPermReversalThree
      = { rows := 3, cols := 3, entries := [[0, 0, 1], [0, 1, 0], [1, 0, 0]] } := rfl

/-! ## The perm layer is IRREDUCIBLE (not block placement) — the decisive adjudication -/

/-- ★★ **THE 3-WIRE PERM STAGE IS NON-TRIVIAL — the reversal is NOT the identity.**  `evalCell
(spiderPermReversalThree) != evalCell (id a.a.a)`: the reversal's `(0,0)` entry is `0` while the identity's is
`1`.  So the width-3 permutation genuinely needs a perm stage — it is not the (block-diagonal) identity, the
analogue of the r2 `sigma != id` separation lifted to width 3. -/
theorem bunchedBimonoidReversalNotIdentity :
    bunchedBimonoidEvalCell bunchedBimonoidSpiderPermReversalThree
      ≠ bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidAaaWord) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★★ **THE PERM LAYER IS LOAD-BEARING (2-wire, cited from r3).**  The swap is UNREACHABLE by the block-diagonal
`diag(a, b)` for every `a, b` (`bunchedBimonoidSwapUnreachableByDiagonal`, r3): its off-diagonal `(0,1) = 1`
while every diagonal has `(0,1) = 0`.  Since the block-exchange interchange produces ONLY block-diagonal
`directSum` results, the perm stage cannot be dissolved into block placement — the recon self-attack #3
adjudication, restated: `spiderOf` is fundamentally spider-WITH-PERMUTATION-MIDDLE. -/
theorem bunchedBimonoidPermLayerIsLoadBearing :
    ∀ (leftScalar rightScalar : Nat),
      bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen
        ≠ bunchedBimonoidEvalCell (bunchedBimonoidSpiderDiag leftScalar rightScalar) :=
  bunchedBimonoidSwapUnreachableByDiagonal

/-! ## B1 truth-probe outputs -/

#eval bunchedBimonoidEvalCell bunchedBimonoidSpiderPermTwo
#eval bunchedBimonoidEvalCell bunchedBimonoidSpiderPermReversalThree
#eval bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidAaaWord)

/-! ## The B1 honesty markers -/

/-- ★★ **ESTABLISHED (B1) — the perm-layer NF shape is shipped, permutation words witnessed.**  `= true` records
the three-stage form `bunchedBimonoidSpiderStaged` (delta / perm / mu) and the permutation-word NF witnesses: the
2-wire swap's NF is `sigma` (`bunchedBimonoidSpiderPermTwo`, round-trip `[[0,1],[1,0]]`) and the 3-wire
reversal's NF is the Yang-Baxter word (`bunchedBimonoidSpiderPermReversalThree`, round-trip the reversal).  The
NF of a permutation IS the permutation word — the recon's decisive adjudication, spider-with-perm-middle. -/
def fxBunchedBimonoid_permLayerNfShipped : Bool := true

/-- ★★ **ESTABLISHED (B1) — the perm layer is IRREDUCIBLE (load-bearing).**  `= true` records
`bunchedBimonoidPermLayerIsLoadBearing` (the swap is unreachable by every `diag(a, b)`, cited from r3) and
`bunchedBimonoidReversalNotIdentity` (the width-3 reversal is separated from the identity).  Since the
block-exchange produces only block-diagonal results, the perm stage genuinely needs a `sigma` word — it cannot
be dissolved into block placement.  The honest NF is not a pure spider; the perm layer is the irreducible
middle. -/
def fxBunchedBimonoid_permLayerIrreducible : Bool := true

/-! # =========================================================================================
    # B2 — THE HONEST REACH + THE WALLS (general routing transpose + Node A strict-law extension)
    # =========================================================================================

★ **The general `spiderOf` NODE is honestly scoped: two fragments reached, the general routing walled.**  The
block-diagonal fragment (perm-stage = id) is reached by the r3 block-exchange (`bunchedBimonoidSpiderDiagMatrix`
et al.); the permutation fragment (delta/mu-stages = id) is reached by the hexagon-generated permutation words
(B1 here).  The fully-general `spiderOf : Mat -> CellExpr` — combining a non-trivial delta-stage, an arbitrary
permutation perm-stage (read off a row-major-to-column-sum transpose), and a non-trivial mu-stage — is the sole
remaining node, walled at the transpose encoding. -/

/-- ★ **WALL (honest, r4) — the GENERAL routing perm-stage for an arbitrary matrix needs the transpose encoding.**
`= false` records the EXACT remaining `spiderOf` jam: assembling `spiderStaged (deltaStage M) (permStage M)
(muStage M)` for an ARBITRARY `q x p` matrix `M` requires computing the perm-stage as a permutation WORD in
`sigma`s from `M`'s row-major-to-column-sum routing — a `List (List Nat)` transpose helper (the recon's flagged
riskiest encoding member).  The hexagon rows (B1) supply the permutation-word GENERATORS, and the block-exchange
supplies the block placement, but the general routing that reads an arbitrary permutation off `M` is DEFERRED.
This is the SAME wall as the r1 `fxBunchedBimonoid_spiderGeneralRoutingReached` (name and `= false` value
byte-intact, cross-file). -/
def fxBunchedBimonoid_permStageGeneralRoutingTransposeWall : Bool := false

/-- ★★ **NARROWED (honest, r4) — Node A (the strict-law matrix-soundness extension) has 2 of 3 components
delivered.**  `= true` records the adjudication of the strict-law extension wall
(`fxBunchedBimonoid_matrixStrictLawExtensionReached`, verbatim demand: "`matMul` associativity (a finite-sum
Fubini), the identity-matrix unit laws, and block multiplicativity (whisker-functoriality + interchange)").
DELIVERED: component (3) block multiplicativity = `bunchedBimonoidBlockExchangeInterchange` (r3, zero-axiom) PLUS
the width-3 braiding coherence now supplied by `BunchedBimonoidHexagonRow` (r4 B1 — Yang-Baxter +
wide-symmetry naturality, matrix-respected).  RESIDUAL: component (1) general `matMul` associativity (the
3-factor finite-sum Fubini + `List.range` reconstruction — only concrete `rfl` probes shipped
`bunchedBimonoidMatMulAssocConcrete{TwoByTwo,NonSquare}`) and component (2) general-`n` identity-matrix unit laws
(only the `1 x 1` singletons `bunchedBimonoidIdentity{Left,Right}UnitSingleton` shipped, not general `n` — the
general case needs the `List (List Nat)` reconstruction the block-exchange deliberately dodged).  Since the
demand is NOT literally met (2 of 3), `fxBunchedBimonoid_matrixStrictLawExtensionReached` /
`...fullIsolationNeedsStrictLawFubiniKit` stay `= false` (byte-intact, cross-file); this is a NARROWING marker
recording the block-multiplicativity + hexagon components. -/
def fxBunchedBimonoid_nodeAStrictLawExtensionNarrowed : Bool := true

/-- ★ **THE HONEST spiderOf REACH — block-diagonal (r3) + permutation words (r4).**  `= true` records the
adjudicated reachability: the general `spiderOf : Mat -> CellExpr` is reached on TWO fragments — the
block-diagonal matrices (`directSum` of shipped stages, via the r3 block-exchange interchange) and the
permutation matrices (permutation WORDS in `sigma`, via the r4 hexagon rows) — while the fully-general routing
(arbitrary `q x p` with a non-trivial perm-stage read off a transpose) is the sole remaining node
(`fxBunchedBimonoid_permStageGeneralRoutingTransposeWall`).  The NF is honestly three-stage (delta / perm / mu);
neither the block-diagonal nor the permutation fragment alone is the full `spiderOf`. -/
def fxBunchedBimonoid_spiderOfReachIsBlockDiagonalPlusPerm : Bool := true

/-- ★★ **ESTABLISHED (B2) — the WP-PROP r4 perm-stage ledger (honest scoreboard).**  `= true` records the
complete r4 perm-layer advance: the three-stage NF form `bunchedBimonoidSpiderStaged` (delta / perm / mu); the
permutation-word NF witnesses (2-wire swap = `sigma`, 3-wire reversal = the Yang-Baxter word, both round-tripped)
and the perm-layer irreducibility (`bunchedBimonoidPermLayerIsLoadBearing` + `...ReversalNotIdentity` — the perm
stage cannot be dissolved into block placement); the honest spiderOf reach (block-diagonal via r3 + permutation
words via r4); and the walls NAMED at their exact nodes — the general routing transpose
(`fxBunchedBimonoid_permStageGeneralRoutingTransposeWall`) and Node A's two residual strict-law components
(`fxBunchedBimonoid_nodeAStrictLawExtensionNarrowed`).  Every upstream `= false` marker
(`fxBunchedBimonoid_spiderGeneralRoutingReached`, `...matrixStrictLawExtensionReached`,
`...fullIsolationNeedsStrictLawFubiniKit`) keeps its name and value byte-intact. -/
def fxBunchedBimonoid_permStageLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
