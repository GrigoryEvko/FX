import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingValleyDescent
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionRainbow
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelPinning

/-! # WalkingString — the `convOfMapEq` PORT, closed MODULO the two named residuals (FC-9, the port-or-wall round)

FC-9 is the final dedicated headline round for the adjoint-triple `convOfMapEq` (the COMPLETENESS field of the
keystone `StringSaturatedMatchingCanonicalization`).  The recon verdict was PORT-UNLIKELY for the unconditional flip,
and the substrate confirms it: every ingredient the port can reach WITHOUT the ~92K-line colour-aware valley
apparatus is already shipped —

  * the free-trace LIFT (`StringSaturatedTwoCellConv.ofSpineTraceEquiv`, `StringMatchingCompleteness`);
  * the monolithic residual `StringMatchingReductsShareSpineTrace` and the completeness reduction
    `stringConvOfMapEq_ofReductsShareSpineTrace` (`StringMatchingCompleteness`);
  * the fuel-structural valley-descent DRIVER `stringValleyDescentDriverCell` and the SHARPENING of the monolithic
    residual into the TWO sub-producers `stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv`
    (`StringMatchingValleyDescent`);
  * the label-pinning CRUX `stringCupCod_ne_capDom` — a string cup's cod word is NEVER a string cap's dom word,
    the r6 word-bookkeeping heart that replaces the adjunction's (FALSE-at-the-string) length-rigidity
    (`StringLabelPinning`);
  * the reconstruction realizable CORE `stringReconstructIdentityForm` / `stringReconstructCrossLevel` and the
    reconstruction-route interface `StringMatchingReconstruction` (`StringMatchingReconstructionRainbow` /
    `StringMatchingReconstructionInterface`).

So this file ships the CRISPEST honest form of the port and then WALLS: it closes `convOfMapEq` — and the whole
adjoint-triple DECISION — MODULO exactly the two named sub-producers, and machine-witnesses the exact two-colour
valley crux configuration that stands between here and the unconditional flip.

## What this file proves (the port, closed modulo `(oracle × valleyTraceEquiv)`)

  * ★ `stringConvOfMapEq_ofOracleAndValleyTraceEquiv` — the BASE `convOfMapEq`: given a per-step descent
    `StringCellDescentStepOracle` (Piece I) AND the cell-level `StringCellValleyTraceEquiv` (Piece II), every
    parallel pair with equal boundary matching is `StringSaturatedTwoCellConv`.  The single-theorem composition of
    the shipped sharpening with the shipped reduction.
  * ★ `stringConvOfColouredMapEq_ofOracleAndValleyTraceEquiv` — its TWO-LEVEL lift (colours collapse to the base).
  * ★ `stringSaturatedMatchingCanonicalization_ofOracleAndValleyTraceEquiv` — the whole two-field keystone
    (soundness r2 + completeness modulo the two sub-producers).
  * ★ `decidableStringSaturatedConv_ofOracleAndValleyTraceEquiv` — the FULL adjoint-triple word-problem DECISION,
    total modulo the two sub-producers.

These make precise, machine-checked, and residual-named the statement "the port is DONE except for the two
colour-aware valley producers".  Neither sub-producer is a `Prop` this file discharges — each is the colour-aware
re-derivation the length-rigidity failure forces, a multi-round arc — so `fxString_hasAdjointTripleCompleteness`
(in `StringMatchingCompleteness`) is NOT moved and stays `false`, honestly.

## The crux configuration, machine-witnessed (the exact two-colour valley)

The one obstruction between here and the flip is Piece II — the colour-aware valley reconstruction — and its heart is
the mixed-colour window the width-only classifier `classifyAdjacentAtoms` (colour-BLIND) would mis-route to the
STRAIGHTEN arm.  This file exhibits it as concrete, computed data:

  * ★ `stringMixedLowerWindow_cannotStraighten` — the general pin `stringCupCod_ne_capDom` applied to the EXACT
    mixed pair `(η, ε')` (lower unit `η` opening `F·G` next to upper counit `ε'` closing `H·G`, both `base ⟶ base`):
    straightening would demand the outer legs reconnect, i.e. `F·G = H·G`, refuted (`stringFG ≠ stringHG`).
  * ★ `stringMixedUpperWindow_cannotStraighten` — the mirror window `(η', ε)` (upper unit `η'` opening `G·H` next to
    lower counit `ε` closing `G·F`, both `tip ⟶ tip`): would demand `G·H = G·F`, refuted (`stringGH ≠ stringGF`).
  * ★★ `stringTwoColourValleyCruxConfiguration` — the exact two-colour valley `stringCrossLevelCell : G·F ⇒ G·H`
    (lower counit `ε`, colour 1, then upper unit `η'`, colour 2) with its computed base matching
    `{2, 2, [1,0,3,2], 0}`, both mixed windows pinned, AND the valley already CANONICAL (zero residual moves to its
    reconstruction).  This is the literature's "disjoint-boundary two-colour case is EASIER" (Di Francesco–Zuber
    far-commutation `|i−j| > 1`): here `ε` and `η'` live on DISJOINT boundaries (`ε` on the `G·F` source, `η'` on
    the `G·H` target), so they commute freely and the valley needs no straightening — the residual is entirely the
    SAME-boundary interleaved case, not this one.

## The wall (Piece II) and the future routes bequeathed

The standing residual is `StringCellValleyTraceEquiv` (`StringMatchingValleyDescent`): two `adjointTripleModeSignature`
valleys with equal `matchingOf` are `SpineTraceEquiv`.  The walking adjunction discharges its analog by length-rigid
atom determination (`cupRestrict_reconstructs`, reading atoms through LENGTHS); at the string this is FALSE
(`string_left_ne_coLeft`: `F`, `H` both length-1, distinct), so the reconstruction must read atoms off the BOUNDARY
labels (which DO determine every valley generator's colour) — a colour-aware re-derivation of the ~92K-line
apparatus.  This is NOT a shared-`G` coherence gap (`fxString_hasAdjointTripleCoherenceGap` stays `false`): colours
are boundary-determined on valleys, so completeness stays colour-BLIND.  It is a genuine PORT of new mathematics —
there is no citable free-adjoint-STRING word-problem normal-form theorem (Schanuel–Street / Riehl–Verity decide only
the SINGLE adjunction; Rosebrugh–Wood recover Δ but prove no NF).  Three candidate future routes:

  * **(a) the comb / word-bookkeeping analogue for interleaved-colour blocks.**  Re-derive the Arc* / SpineValley*
    width-0 / mid-0 / positive bricks with `generatorDom`/`generatorCod` word-reading in place of length-reading,
    block-by-block per colour.  Grounded in Landau's middle-pattern unique decomposition `D = Dᵢₙ ∘ m(D) ∘ D_fin`
    (Pacific J. Math. 197(2), 2001; Bisch–Jones `k=1`, "a straightforward generalization" for `k`) and the
    Di Francesco–Zuber trace-monoid commutation (hep-th/9807074: far generators `|i−j| > 1` and adjacent generators
    with colour-index sum `≤ k` commute FREELY; only same-adjacent-boundary with over-full sum `m+l > k` needs the
    cubic "comb" relation).  The two-colour disjoint case is EASIER — the new work is exactly the same-boundary
    interleaved window.
  * **(b) the Δ / simplicial route the monad lane used.**  Model each single adjunction's valley by its
    `Delta`/`MonadDeltaModel` monotone fold, glue the two at the shared `G` — mirroring the Brauer-lane comb fold
    that flipped its master.  Published construction order: an increasing NON-CROSSING chain of monochromatic chord
    diagrams, coarsest species outermost (arXiv:2507.23460; Bisch–Jones free-product nesting).
  * **(c) the #2021 idempotent-quadruple pivot (`ʃ ⊣ ♭ ⊣ ♯`) — the recommended cheapest target.**  Idempotency makes
    the outer modalities property-like ⟹ homs thin ⟹ the sister lane's `idempotentThinness_ofNormalize`
    (`WalkingIdempotent/`) collapses "matching-equal ⟹ convertible" to a boundary-determined normalizer, BYPASSING
    valley descent entirely (spec in `StringLabelPinning` header, §the #2021 pivot).

Lane status after FC-9: SOUNDNESS DECIDED (r2); COMPLETENESS the port CLOSED MODULO the two named sub-producers
(this file), the unconditional flip PAUSED at the colour-aware Piece-II valley reconstruction, research-grade, with
the exact remaining site machine-witnessed and the routes bequeathed.  The lane PAUSES here pending the #2021 pivot.

Raw Lean 4 + Init; the conditional port is a two-line composition of shipped lemmas, the crux witnesses are the
shipped pin applied to the named generators plus shipped `rfl`/triangle evals.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The port — `convOfMapEq` closed modulo `(StringCellDescentStepOracle × StringCellValleyTraceEquiv)` -/

/-- ★ **The BASE `convOfMapEq`, modulo the two named sub-producers.**  Given the per-step descent oracle (Piece I)
AND the cell-level valley trace-equivalence (Piece II), every parallel pair with equal boundary matching is
`StringSaturatedTwoCellConv`.  The single-theorem composition of the shipped sharpening
(`stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv`) with the shipped completeness reduction
(`stringConvOfMapEq_ofReductsShareSpineTrace`) — the crispest honest form of the FC-9 port: DONE except for the two
colour-aware valley producers. -/
theorem stringConvOfMapEq_ofOracleAndValleyTraceEquiv
    (oracle : StringCellDescentStepOracle) (valleyTraceEquiv : StringCellValleyTraceEquiv)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofReductsShareSpineTrace
    (stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv oracle valleyTraceEquiv)
    cellA cellB matchingsEqual

/-- ★ **The TWO-LEVEL `convOfMapEq`, modulo the two sub-producers.**  Equal `ColouredDiagramType` of a parallel pair
projects (on the nose) to equal base `matchingOf`, so the two-level completeness IS the base one — colours never
enter the reconstruction (completeness is colour-BLIND). -/
theorem stringConvOfColouredMapEq_ofOracleAndValleyTraceEquiv
    (oracle : StringCellDescentStepOracle) (valleyTraceEquiv : StringCellValleyTraceEquiv)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (colouredMatchingsEqual :
      colouredMatchingOf sourcePath targetPath cellA = colouredMatchingOf sourcePath targetPath cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfColouredMapEq_ofReductsShareSpineTrace
    (stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv oracle valleyTraceEquiv)
    cellA cellB colouredMatchingsEqual

/-- ★ **The whole keystone, modulo the two sub-producers** — soundness (r2, unconditional) + completeness (from the
oracle and the valley trace-equivalence), the two-field `StringSaturatedMatchingCanonicalization`. -/
def stringSaturatedMatchingCanonicalization_ofOracleAndValleyTraceEquiv
    (oracle : StringCellDescentStepOracle) (valleyTraceEquiv : StringCellValleyTraceEquiv) :
    StringSaturatedMatchingCanonicalization :=
  stringSaturatedMatchingCanonicalization_ofReducts
    (stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv oracle valleyTraceEquiv)

/-- ★★ **The FULL adjoint-triple word-problem DECISION, total modulo the two sub-producers.**  Compare the two
cells' `ColouredDiagramType` by the derived `DecidableEq` (it COMPUTES): equal ⟹ `isTrue` via the two-level
completeness above; unequal ⟹ `isFalse`, since the UNCONDITIONAL r2 soundness would force the coloured matchings
equal.  The `isFalse` leg is residual-FREE (uses only r2); the `isTrue` leg is gated on the two sub-producers. -/
def decidableStringSaturatedConv_ofOracleAndValleyTraceEquiv
    (oracle : StringCellDescentStepOracle) (valleyTraceEquiv : StringCellValleyTraceEquiv)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofReducts
    (stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv oracle valleyTraceEquiv)
    cellA cellB

/-! ## The crux configuration, machine-witnessed (the exact two-colour valley) -/

/-- ★ **The mixed LOWER window cannot straighten** — the general pin `stringCupCod_ne_capDom` applied to the EXACT
mixed pair `(η, ε')`: the lower unit `η = StringTwoCell.unitLower` (a cup opening `F·G`) next to the upper counit
`ε' = StringTwoCell.counitUpper` (a cap closing `H·G`), both between `base ⟶ base`.  The width-only classifier could
route this shared-leg pair to the STRAIGHTEN arm, whose band collapse then demands the outer legs reconnect
(`cupCod = capDom`, i.e. `F·G = H·G`) — refuted here (`stringFG ≠ stringHG`).  The concrete instance of the r6 pin
firing on the named mixed window. -/
theorem stringMixedLowerWindow_cannotStraighten : stringFG ≠ stringHG :=
  stringCupCod_ne_capDom StringTwoCell.unitLower StringTwoCell.counitUpper rfl rfl

/-- ★ **The mixed UPPER window cannot straighten** — the mirror pair `(η', ε)`: the upper unit
`η' = StringTwoCell.unitUpper` (a cup opening `G·H`) next to the lower counit `ε = StringTwoCell.counitLower` (a cap
closing `G·F`), both between `tip ⟶ tip`.  Straightening would demand `G·H = G·F`, refuted (`stringGH ≠ stringGF`).
The second mixed window pinned by the same crux. -/
theorem stringMixedUpperWindow_cannotStraighten : stringGH ≠ stringGF :=
  stringCupCod_ne_capDom StringTwoCell.unitUpper StringTwoCell.counitLower rfl rfl

/-- ★★ **The exact two-colour valley crux configuration, machine-witnessed.**  The cross-level valley
`stringCrossLevelCell : G·F ⇒ G·H` (lower counit `ε`, colour 1, vertically composed with upper unit `η'`, colour 2)
is the canonical two-colour valley; this bundle exhibits, as computed data, EVERYTHING the wall rests on:

  * its base boundary matching computes to `{2, 2, [1,0,3,2], 0}` — a genuine two-arc cross-level diagram;
  * BOTH mixed cup·cap windows are pinned (`stringFG ≠ stringHG`, `stringGH ≠ stringGF`) — the straighten arm cannot
    fire across colours;
  * the valley is ALREADY canonical (`stringCrossLevelCell ≈ stringReconstructCrossLevel`, zero residual moves), i.e.
    its two atoms `ε` and `η'` live on DISJOINT boundaries (`ε` on the `G·F` source, `η'` on the `G·H` target) and
    commute freely — the literature's "disjoint-boundary two-colour case is EASIER" (Di Francesco–Zuber
    far-commutation).  The standing residual is entirely the SAME-boundary interleaved case, NOT this one. -/
theorem stringTwoColourValleyCruxConfiguration :
    matchingOf stringReconstructCrossLevel
        = { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 }
      ∧ stringFG ≠ stringHG
      ∧ stringGH ≠ stringGF
      ∧ StringSaturatedTwoCellConv stringCrossLevelCell stringReconstructCrossLevel :=
  ⟨stringReconstructCrossLevel_matchingOf, stringMixedLowerWindow_cannotStraighten,
    stringMixedUpperWindow_cannotStraighten, stringReconstruct_crossLevel_convToReconstruct⟩

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the `convOfMapEq` port is CLOSED MODULO the two named sub-producers.**  The base completeness
`stringConvOfMapEq_ofOracleAndValleyTraceEquiv`, its two-level lift, the whole keystone
`stringSaturatedMatchingCanonicalization_ofOracleAndValleyTraceEquiv`, and the FULL decision
`decidableStringSaturatedConv_ofOracleAndValleyTraceEquiv` all follow — zero-axiom, one composition each — from the
per-step descent `StringCellDescentStepOracle` (Piece I) AND the cell-level `StringCellValleyTraceEquiv` (Piece II).
Everything the port can reach without the colour-aware valley apparatus is shipped; the residual is exactly the two
producers, machine-named.  The crux configuration is machine-witnessed on the exact two-colour valley
(`stringTwoColourValleyCruxConfiguration`): both mixed windows pinned by the r6 crux, the valley already canonical.
`= true`. -/
def fxString_hasConvOfMapEqPortModuloTwoResiduals : Bool := true

/-- **OPEN (honest) — the UNCONDITIONAL `convOfMapEq` flip is PAUSED at the colour-aware Piece-II valley
reconstruction; NO marker moved.**  `stringConvOfMapEq_ofOracleAndValleyTraceEquiv` needs the two sub-producers, and
neither ports by instantiation: the string quiver is NOT length-rigid (`fxString_hasStringLengthRigidityFailure`), so
the STRAIGHTEN band collapse and the Piece-II valley reconstruction — both resting on the adjunction's
`adjunctionPath_eq_of_length_eq` — must be re-derived colour-aware, reading atoms off the BOUNDARY labels rather than
lengths.  This is a genuine PORT of new mathematics (no citable free-adjoint-STRING word-problem NF theorem), NOT a
shared-`G` coherence gap (`fxString_hasAdjointTripleCoherenceGap` stays `false`).  The lane PAUSES here; the future
routes are bequeathed in the file header (comb / word-bookkeeping per Landau + Di Francesco–Zuber; the Δ/simplicial
glue the monad lane used; and the recommended #2021 idempotent-quadruple thinness pivot via
`idempotentThinness_ofNormalize`).  `fxString_hasAdjointTripleCompleteness` (in `StringMatchingCompleteness`) is NOT
moved and stays `false`.  `= false`. -/
def fxString_hasConvOfMapEqPortFlip : Bool := false

end FX1Poly.Polygraph
