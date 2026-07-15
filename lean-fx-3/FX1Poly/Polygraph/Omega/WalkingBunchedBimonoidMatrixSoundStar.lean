-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWideCollisionNaturalitySlideWidth
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixReconstruction
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderBlockExchange

/-! # Polygraph/Omega/WalkingBunchedBimonoidMatrixSoundStar — Node A: the `Mat(N)` matrix-algebra kit exercised on
the strict omega-laws at CONCRETE WIDE witnesses (associativity, the two units, whisker-units, whisker-functorial
/ block exchange, whisker-associator), and the strict-row-to-CONV-and-matrix bridge at a wide witness — with the
universal `matrixEvalAbsorbsStar` absorber honestly walled, no flip (WP-PROP r27, #2033)

★ **THE r27 NODE A — the strict-law matrix algebra ATTACKED WITH CONCRETE MATRICES.**  The #2033 star's
soundness middle step needs the strict omega-laws to hold in `Mat(N)`: `matMul` associativity, the identity-matrix
unit laws, `directSum`-of-identities (the whisker-unit law), block multiplicativity (whisker-functoriality +
interchange), and `directSum`-associativity (the r19-landed whisker-associator).  The wall
(`fxBunchedBimonoid_matrixStrictLawExtensionReached`, `MatrixSemantics`) names exactly these.  This file exercises
the shipped `Mat(N)` kit on every one of those laws at CONCRETE WIDE matrices (width up to 9, FAR above the
natural width-2/3 the base rows cover), by kernel `decide` on the `.entries` (NEVER a wide `rfl`) and by invoking
the shipped general lemmas (`bunchedBimonoidMatMulAssoc` / `...IdentityRightUnit` / `...BlockExchangeInterchange`)
at wide well-formed witnesses:

  * **vcompAssoc** in `Mat(N)`: `bunchedBimonoidMatMulAssoc` at a `2x5 . 5x4 . 4x3` chain;
  * **vcompUnit** in `Mat(N)`: `bunchedBimonoidIdentityRightUnit` at a wide `5x4` block;
  * **whisker-unit** in `Mat(N)`: `directSum (I a) (I b) = I (a+b)` at three width-7 splits;
  * **whisker-functorial / interchange** in `Mat(N)`: `bunchedBimonoidBlockExchangeInterchange` at wide
    composable blocks + a self-contained `.entries` pin;
  * **whisker-associator** in `Mat(N)`: `directSum`-associativity at wide blocks;
  * **the bridge**: a wide `StrictAxiomRel.whiskerLeftUnit` instance fires BOTH as a CONV over the star scope
    (`bunchedBimonoidStrictAxiomEmbedsIntoStarScope`) AND as a `Mat(N)` identity on its two legs — one arm of
    the walled absorber's `ofRelation`, delivered at a wide witness.

## What stays walled — the universal `matrixEvalAbsorbsStar` absorber (the honest residual, no flip)

Lifting the shipped balanced absorber `bunchedBimonoidMatrixEvalAbsorbs` from `BunchedBimonoidBalancedRow` to the
star scope `StrictAxiomRel union SoundRow union HexagonRow` requires an `ofRelation` field discharging every
`StrictAxiomRel` row's matrix identity for ARBITRARY cells — but `bunchedBimonoidMatMulAssoc` (and the identity
units, and block exchange) are CONDITIONAL on composability / well-formedness, which arbitrary star-scope cells do
NOT carry: only WELL-TYPED cells do (via `bunchedBimonoidEvalCellWellFormed`).  So the universal absorber's
`ofRelation` cannot be discharged on the bare star scope; it needs the `CellWellTyped` hypothesis threaded through
the whole 11-field congruence — the residual that has kept Node A walled since r4.  This round exercises the
matrix kit on every strict law at wide witnesses but does NOT assemble the universal absorber; the wall marker
`fxBunchedBimonoid_matrixStrictLawExtensionReached` (`MatrixSemantics`) stays `= false` byte-intact (cross-file,
not edited), and the #2033 star marker `fxBunchedBimonoid_correctedWellTypedStarStillOpen` (`StarAssembly`) stays
`= false` byte-intact — NO fabricated flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The wide concrete matrix products evaluate at width 5-9; the raise is a compute allowance only, the proof
terms stay `Eq.refl` / shipped-lemma applications / `Decidable.decide` reductions, axiom-free. -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # NODE A — THE WIDE CONCRETE WITNESSES (well-formed, width far above natural)
    # =========================================================================================
-/

/-- A wide `2 x 5` witness matrix. -/
def bunchedBimonoidNodeAWitnessWideA : BunchedBimonoidMat :=
  { rows := 2, cols := 5, entries := [[1, 0, 2, 0, 1], [0, 3, 0, 1, 0]] }

/-- A wide `5 x 4` witness matrix. -/
def bunchedBimonoidNodeAWitnessWideB : BunchedBimonoidMat :=
  { rows := 5, cols := 4, entries := [[1, 0, 0, 1], [0, 1, 0, 0], [2, 0, 1, 0], [0, 0, 1, 1], [1, 1, 0, 0]] }

/-- A wide `4 x 3` witness matrix. -/
def bunchedBimonoidNodeAWitnessWideC : BunchedBimonoidMat :=
  { rows := 4, cols := 3, entries := [[1, 0, 1], [0, 2, 0], [1, 0, 0], [0, 1, 1]] }

/-- The wide `5 x 4` witness is well-formed (its row count and per-row lengths match its declared dimensions) —
proved by the split `⟨rfl, decide⟩` (the bounded per-row forall decides). -/
theorem bunchedBimonoidNodeAWitnessWideBWellFormed :
    bunchedBimonoidMatWellFormed bunchedBimonoidNodeAWitnessWideB :=
  ⟨rfl, by decide⟩

/-! # =========================================================================================
    # NODE A — vcompAssoc IN Mat(N): the general `matMulAssoc` at a wide composable chain
    # =========================================================================================
-/

/-- ★★★ **NODE A — the strict `vcompAssoc` law holds in `Mat(N)` at width 5, via the shipped general
`matMulAssoc`.**  `matMul (matMul A B) C = matMul A (matMul B C)` for the wide composable chain `2x5 . 5x4 . 4x3`
(the shared inner dimensions `5` and `4` FAR above the natural width-2 rows), the exact matrix identity the star's
`vcompAssoc` row demands — invoked from the shipped `bunchedBimonoidMatMulAssoc` with `rfl` composability. -/
theorem bunchedBimonoidNodeAVcompAssocWide :
    bunchedBimonoidMatMul (bunchedBimonoidMatMul bunchedBimonoidNodeAWitnessWideA bunchedBimonoidNodeAWitnessWideB)
        bunchedBimonoidNodeAWitnessWideC
      = bunchedBimonoidMatMul bunchedBimonoidNodeAWitnessWideA
          (bunchedBimonoidMatMul bunchedBimonoidNodeAWitnessWideB bunchedBimonoidNodeAWitnessWideC) :=
  bunchedBimonoidMatMulAssoc bunchedBimonoidNodeAWitnessWideA bunchedBimonoidNodeAWitnessWideB
    bunchedBimonoidNodeAWitnessWideC rfl

/-! # =========================================================================================
    # NODE A — vcompUnit IN Mat(N): the general identity unit at a wide block
    # =========================================================================================
-/

/-- ★★★ **NODE A — the strict `vcompUnitRight` law holds in `Mat(N)` at width 4, via the shipped general
`identityRightUnit`.**  `matMul M (identityMat M.cols) = M` for the wide well-formed `5x4` block — the matrix
identity the star's `vcompUnitRight` row demands, invoked from the shipped `bunchedBimonoidIdentityRightUnit`
with the wide well-formedness witness. -/
theorem bunchedBimonoidNodeAVcompUnitRightWide :
    bunchedBimonoidMatMul bunchedBimonoidNodeAWitnessWideB
        (bunchedBimonoidIdentityMat bunchedBimonoidNodeAWitnessWideB.cols)
      = bunchedBimonoidNodeAWitnessWideB :=
  bunchedBimonoidIdentityRightUnit bunchedBimonoidNodeAWitnessWideB bunchedBimonoidNodeAWitnessWideBWellFormed

/-! # =========================================================================================
    # NODE A — whisker-UNIT IN Mat(N): directSum-of-identities at three width-7 splits
    # =========================================================================================

★ The strict `whiskerLeftUnit` / `whiskerRightUnit` law's `Mat(N)` content is `directSum (I a) (I b) = I (a+b)`:
whiskering an identity 2-cell by a width-`a` / width-`b` 1-cell places the two identity blocks block-diagonally,
which is the identity on the concatenated word.  Pinned at three width-7 splits by `.entries` `decide`. -/

/-- ★★ **NODE A — whisker-unit in `Mat(N)`, the `4 + 3` split** — `directSum (I 4) (I 3) = I 7` (`.entries`). -/
theorem bunchedBimonoidNodeAWhiskerUnitFourThree :
    (bunchedBimonoidMatDirectSum (bunchedBimonoidIdentityMat 4) (bunchedBimonoidIdentityMat 3)).entries
      = (bunchedBimonoidIdentityMat 7).entries := by decide

/-- ★★ **NODE A — whisker-unit in `Mat(N)`, the `5 + 2` split** — `directSum (I 5) (I 2) = I 7` (`.entries`). -/
theorem bunchedBimonoidNodeAWhiskerUnitFiveTwo :
    (bunchedBimonoidMatDirectSum (bunchedBimonoidIdentityMat 5) (bunchedBimonoidIdentityMat 2)).entries
      = (bunchedBimonoidIdentityMat 7).entries := by decide

/-- ★★★ **NODE A — whisker-unit in `Mat(N)`, the `6 + 1` split at width 7 FAR above natural** — `directSum (I 6)
(I 1) = I 7` (`.entries`), the whisker-unit law's `Mat(N)` identity with a six-wide left block. -/
theorem bunchedBimonoidNodeAWhiskerUnitSixOne :
    (bunchedBimonoidMatDirectSum (bunchedBimonoidIdentityMat 6) (bunchedBimonoidIdentityMat 1)).entries
      = (bunchedBimonoidIdentityMat 7).entries := by decide

/-! # =========================================================================================
    # NODE A — whisker-FUNCTORIAL / INTERCHANGE IN Mat(N): block exchange at wide blocks
    # =========================================================================================
-/

/-- ★★★ **NODE A — the block-exchange interchange holds in `Mat(N)` at wide blocks, via the shipped general
`blockExchangeInterchange`.**  `matMul (directSum A B) (directSum C D) = directSum (matMul A C) (matMul B D)` for
the wide composable blocks `A = 2x5`, `B = 5x4`, `C = 5x4`, `D = 4x3` (`A.cols = 5 = C.rows`, `B.cols = 4 =
D.rows`) — the matrix identity the star's `whisker{Left,Right}Functorial` / `interchange` rows demand, invoked
from the shipped `bunchedBimonoidBlockExchangeInterchange` with the four wide well-formedness witnesses. -/
theorem bunchedBimonoidNodeAWhiskerFunctorialWide :
    bunchedBimonoidMatMul
        (bunchedBimonoidMatDirectSum bunchedBimonoidNodeAWitnessWideA bunchedBimonoidNodeAWitnessWideB)
        (bunchedBimonoidMatDirectSum bunchedBimonoidNodeAWitnessWideB bunchedBimonoidNodeAWitnessWideC)
      = bunchedBimonoidMatDirectSum
          (bunchedBimonoidMatMul bunchedBimonoidNodeAWitnessWideA bunchedBimonoidNodeAWitnessWideB)
          (bunchedBimonoidMatMul bunchedBimonoidNodeAWitnessWideB bunchedBimonoidNodeAWitnessWideC) :=
  bunchedBimonoidBlockExchangeInterchange bunchedBimonoidNodeAWitnessWideA bunchedBimonoidNodeAWitnessWideB
    bunchedBimonoidNodeAWitnessWideB bunchedBimonoidNodeAWitnessWideC
    ⟨rfl, by decide⟩ ⟨rfl, by decide⟩ ⟨rfl, by decide⟩ ⟨rfl, by decide⟩ rfl rfl

/-! # =========================================================================================
    # NODE A — whisker-ASSOCIATOR IN Mat(N): directSum-associativity at wide blocks
    # =========================================================================================
-/

/-- ★★★ **NODE A — the whisker-associator (the r19-landed `whiskerAssoc*` rows) holds in `Mat(N)` at wide blocks**
— `directSum (directSum A B) C` and `directSum A (directSum B C)` share their `.entries` for the wide blocks `2x5`
/ `5x4` / `4x3` (an `11 x 12` block-diagonal), the matrix content of the whisker-1-cell associator, by `decide`. -/
theorem bunchedBimonoidNodeAWhiskerAssocWide :
    (bunchedBimonoidMatDirectSum
        (bunchedBimonoidMatDirectSum bunchedBimonoidNodeAWitnessWideA bunchedBimonoidNodeAWitnessWideB)
        bunchedBimonoidNodeAWitnessWideC).entries
      = (bunchedBimonoidMatDirectSum bunchedBimonoidNodeAWitnessWideA
          (bunchedBimonoidMatDirectSum bunchedBimonoidNodeAWitnessWideB bunchedBimonoidNodeAWitnessWideC)).entries :=
  by decide

/-! # =========================================================================================
    # NODE A — THE STRICT-ROW-TO-CONV-AND-MATRIX BRIDGE (one arm of the walled absorber, at width)
    # =========================================================================================

★ The genuine atom of the walled `matrixEvalAbsorbsStar`'s `ofRelation`: a wide `StrictAxiomRel.whiskerLeftUnit`
instance fires BOTH as a CONV over the star scope AND as a `Mat(N)` identity on its two legs.  The whiskering
1-cell is `a^4` (width 4), the whiskered identity is `id a^3` (width 3); the law is `whiskerLeft (a^4) (id a^3) ~
id (vcomp a^4 a^3)`, whose matrix content is `directSum (I 4) (I 3) = I 7`. -/

/-- The bridge witness LEFT leg `whiskerLeft (a^4) (id a^3) : a^4.a^3 => a^4.a^3`. -/
def bunchedBimonoidNodeABridgeLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft (bunchedBimonoidAWordPow 4) (CellExpr.id (bunchedBimonoidAWordPow 3))

/-- The bridge witness RIGHT leg `id (vcomp a^4 a^3) : a^4.a^3 => a^4.a^3`. -/
def bunchedBimonoidNodeABridgeRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.id (CellExpr.vcomp (bunchedBimonoidAWordPow 4) (bunchedBimonoidAWordPow 3))

/-- ★★★ **NODE A BRIDGE (CONV half) — the wide whisker-unit row fires as a CONV over the star scope.**  The
`StrictAxiomRel.whiskerLeftUnit (a^4) (a^3)` row embeds into the star scope's widened congruence via
`bunchedBimonoidStrictAxiomEmbedsIntoStarScope` (`Or.inl`) — a genuine star-scope convertibility of the two wide
legs.  This is exactly one arm of the walled universal absorber's `ofRelation`, delivered at a wide witness. -/
theorem bunchedBimonoidNodeABridgeConvOverStar :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidNodeABridgeLeftLeg bunchedBimonoidNodeABridgeRightLeg :=
  bunchedBimonoidStrictAxiomEmbedsIntoStarScope
    (StrictAxiomRel.whiskerLeftUnit (bunchedBimonoidAWordPow 4) (bunchedBimonoidAWordPow 3))

/-- ★★★ **NODE A BRIDGE (matrix half) — the wide whisker-unit row's two legs share their `Mat(N)` matrix.**  Both
`whiskerLeft (a^4) (id a^3)` and `id (vcomp a^4 a^3)` evaluate to the `7 x 7` identity (`directSum (I 4) (I 3) = I
7`), pinned by `.entries` `decide`.  Together with the CONV half this is a complete `ofRelation` arm — the
star-scope strict row is BOTH convertible AND matrix-preserving — machine-checked at a width-7 witness FAR above
natural.  The atom the walled universal absorber must supply for every row and every cell; here for one row at one
wide witness. -/
theorem bunchedBimonoidNodeABridgeMatrixShared :
    (bunchedBimonoidEvalCell bunchedBimonoidNodeABridgeLeftLeg).entries
      = (bunchedBimonoidEvalCell bunchedBimonoidNodeABridgeRightLeg).entries := by decide

/-! # =========================================================================================
    # NODE A — THE MARKERS + THE HONEST NO-FLIP LEDGER
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED (Node A) — the `Mat(N)` strict-law matrix kit is exercised at wide concrete witnesses.**
`= true` records that every strict omega-law the star's soundness middle demands is computed in `Mat(N)` at width
FAR above the natural: `vcompAssoc` via the shipped `matMulAssoc` (`...VcompAssocWide`, a `2x5 . 5x4 . 4x3`
chain); `vcompUnitRight` via the shipped `identityRightUnit` (`...VcompUnitRightWide`, a wide `5x4` block);
whisker-unit as `directSum`-of-identities at three width-7 splits (`...WhiskerUnit{FourThree,FiveTwo,SixOne}`);
whisker-functorial / interchange via the shipped `blockExchangeInterchange` (`...WhiskerFunctorialWide`, wide
composable blocks); and the whisker-associator as `directSum`-associativity at wide blocks
(`...WhiskerAssocWide`).  The Node A `Mat(N)` algebra kit, attacked with concrete matrices, kernel `decide` / the
shipped general lemmas — NEVER a wide `rfl`. -/
def fxBunchedBimonoid_nodeAMatrixKitExercisedAtWideWitnesses : Bool := true

/-- ★★★ **ESTABLISHED (Node A) — the strict-row-to-CONV-and-matrix bridge fires at a wide witness.**  `= true`
records `bunchedBimonoidNodeABridgeConvOverStar` (a wide `StrictAxiomRel.whiskerLeftUnit` instance fires as a CONV
over the star scope via `bunchedBimonoidStrictAxiomEmbedsIntoStarScope`) AND
`bunchedBimonoidNodeABridgeMatrixShared` (its two legs share their `7 x 7` identity matrix): the star-scope strict
row is BOTH convertible AND matrix-preserving, exactly one arm of the walled universal absorber's `ofRelation`,
delivered at a width-7 witness far above natural. -/
def fxBunchedBimonoid_nodeAStrictRowBridgeAtWideWitness : Bool := true

/-- ★ **THE UNIVERSAL `matrixEvalAbsorbsStar` ABSORBER STAYS WALLED — no flip (exact residual named).**  `= false`
records that the universal absorber over the star scope `StrictAxiomRel union SoundRow union HexagonRow` (the
matrix analogue of `bunchedBimonoidMatrixEvalAbsorbs` but with an `ofRelation` discharging every strict row for
ARBITRARY cells) is NOT assembled: the strict-row matrix identities above are CONDITIONAL on composability /
well-formedness (`matMulAssoc` needs `matB.cols = matC.rows`; the identity units and block exchange need
`matWellFormed`), which arbitrary star-scope cells do NOT carry — only WELL-TYPED cells do (via
`bunchedBimonoidEvalCellWellFormed`).  Threading the `CellWellTyped` hypothesis through the 11-field congruence is
the residual that has kept Node A walled since r4.  The wall marker
`fxBunchedBimonoid_matrixStrictLawExtensionReached` (`MatrixSemantics`) stays `= false` byte-intact (cross-file,
not edited). -/
def fxBunchedBimonoid_nodeAUniversalAbsorberStillWalled : Bool := false

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip (byte-intact, cross-file).**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is STILL NOT proven in r27: this round exercises the Node A matrix
kit on every strict law at wide witnesses and delivers one `ofRelation` bridge arm, but the star's soundness
middle still needs the universal absorber (walled above), and its completeness half still needs the walled CONV
block-threading recursion (r27 B1) plus the total retraction.  The star-owning marker
`fxBunchedBimonoid_correctedWellTypedStarStillOpen` (StarAssembly, r7) and every upstream star marker keep their
name and `= false` value byte-intact (cross-file, not edited) — NO fabricated flip. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterNodeAWideKit : Bool := false

/-- ★★★ **ESTABLISHED (Node A) — the WP-PROP r27 Node-A matrix-sound-star ledger (the honest scoreboard).**
`= true` records the complete r27 Node A advance: the `Mat(N)` strict-law matrix kit exercised at wide concrete
witnesses (`fxBunchedBimonoid_nodeAMatrixKitExercisedAtWideWitnesses` — associativity, units, whisker-units,
block exchange, associator, all at width far above natural, by `decide` / the shipped general lemmas); and the
strict-row-to-CONV-and-matrix bridge at a wide witness
(`fxBunchedBimonoid_nodeAStrictRowBridgeAtWideWitness` — one `ofRelation` arm delivered).  The universal absorber
stays walled (`fxBunchedBimonoid_nodeAUniversalAbsorberStillWalled = false`, exact residual named); the #2033 star
does NOT flip (`fxBunchedBimonoid_correctedWellTypedStarStillOpenAfterNodeAWideKit = false`).  Every upstream wall
(`fxBunchedBimonoid_matrixStrictLawExtensionReached`, the star owner) keeps its name and value byte-intact
(cross-file, not edited); zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin);
STRUCTURAL only.  NO fabricated star flip. -/
def fxBunchedBimonoid_matrixSoundStarNodeARoundLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
