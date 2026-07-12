import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSeed
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExprDecidableEq

/-! # WalkingString — the LABEL-PINNING crux (the r6 word-bookkeeping heart, machine-checked)

Rounds r4/r5 NAMED the exact obstruction to porting the adjunction's valley-descent to the three-generator seed:
the walking adjoint-triple quiver is NOT length-rigid (`fxString_hasStringLengthRigidityFailure`).  The adjunction's
`adjunctionPath_eq_of_length_eq` (parallel 1-cells of equal LENGTH are EQUAL — one modality per mode) underpins both
sub-producers of the completeness residual; at the string signature it is FALSE, because out of `base` there are TWO
length-1 modalities `F = left` and `H = coLeft`, DISTINCT (`string_left_ne_coLeft`).

The r6 thesis is: length-rigidity was a CONVENIENCE, not a necessity.  For PARALLEL string cells the source/target
paths are FIXED literal words in `{F, G, H}`, and each generating 2-cell carries its boundary word LITERALLY
(`StringTwoCell.unitLower` opens `F·G`, `unitUpper` opens `G·H`, `counitLower` closes `G·F`, `counitUpper` closes
`H·G`).  So the equalities that length-rigidity used to provide become CONSTRUCTIVE bookkeeping on those literal
words.  The mathematical HEART of that bookkeeping — the fact the whole label-driven staircase rests on — is one
concrete, machine-checkable statement:

  ★ **A cup's cod word is NEVER a cap's dom word** (`stringCupCod_ne_capDom`).  In the walking adjoint triple the
    cups open `{F·G, G·H}` and the caps close `{G·F, H·G}`, and these two two-letter alphabets are DISJOINT:
      * comparable at `base ⟶ base`: `F·G ≠ H·G`  (first letter `F ≠ H`),
      * comparable at `tip ⟶ tip`:   `G·H ≠ G·F`  (second letter `H ≠ F`).
    Both reductions are the SAME fact `left ≠ coLeft` propagated into the words — the exact content the
    length-rigid adjunction got for free but the string must EARN.

## Why this is the pin the r4/r5 rounds owed

The r4 honest-wall record named `stringSharedLegForcesSameColour` as the genuine new node the length-rigidity
failure forces: the width-only classifier `classifyAdjacentAtoms` (colour-BLIND) can route a MIXED-colour adjacent
pair — a lower cup `η` (opens `F·G`) next to an upper cap `ε'` (closes `H·G`) with matching shared-leg widths — to
the `zigZagSharedLeg` STRAIGHTEN arm, whose band collapse then DEMANDS the outer legs reconnect, i.e. the cup's cod
word equal the cap's dom word.  `stringCupCod_ne_capDom` is exactly the refutation: that reconnection would force
`F·G = H·G` hence `F = H`, FALSE.  So a shared-leg cup·cap in the string can only reconnect when the two words
coincide, which across colours they never do — the straighten arm CANNOT fire on a mixed-colour pair.  This is the
"positions are pinned" fact the r6 recon's early-check verified: there is NO counterexample (two parallel
equal-matching cells that fire atoms at essentially-incompatible positions), because a cup and a cap that would need
the same leg have literally distinct words unless they are the same colour.

## What this file does NOT do (the flag stays `false` — honestly)

Shipping the pin does NOT flip `fxString_hasAdjointTripleCompleteness`.  Inhabiting the per-step
`StringCellDescentStepOracle` (Piece I) still requires re-deriving the whole colour-aware STRAIGHTEN assembly +
COMMUTE producer, and proving `StringCellValleyTraceEquiv` (Piece II) still requires the colour-aware valley
reconstruction — both are the ~92K-line `adjunctionModeSignature`-hardcoded valley apparatus re-derived with word
bookkeeping in place of length reconstruction, a genuinely MULTI-ROUND arc.  This file lands the ONE concrete lemma
that both re-derivations consume (the pin the width-only classifier cannot supply), machine-checked and zero-axiom;
it does not port the apparatus.  Soundness stays DECIDED (r2, `fxString_hasAdjointTripleSoundness`); completeness
stays OPEN, research-grade, with the pin now shipped and the exact remaining site (the colour-aware oracle +
Piece II) named.

## The #2021 pivot (spec, for the next round) — the cohesion quadruple rides thinness, not raw triple completeness

The recommended next target is NOT to grind the multi-round string triple completeness but to pivot to the cohesion
QUADRUPLE `ʃ ⊣ ♭ ⊣ ♯` (#2021).  The quadruple adds IDEMPOTENCY: `ʃ` is a comonad, `♯` a monad, so both are
PROPERTY-LIKE modalities (Rijke–Shulman–Spitters, *Modalities in homotopy type theory*, arXiv:1706.07526 — a
reflective subuniverse's modal-membership is an hProp; nLab *idempotent monad*: an algebra structure is unique when
it exists).  Property-like modalities make homs POSETAL/thin, so completeness needs NO valley-descent /
trace-equivalence reconstruction at all — thinness collapses "matching-equal ⟹ convertible" to "any two parallel
cells with a boundary-determined normal form are equal".

  * **Presentation.**  The quadruple = two adjacent adjunctions `ʃ ⊣ ♭` and `♭ ⊣ ♯` SHARING the middle `♭` (exactly
    the string's `F ⊣ G ⊣ H` sharing `G`), PLUS two IDEMPOTENCY rows (`ʃʃ ≅ ʃ`, `♯♯ ≅ ♯`) as extra saturation
    constructors on the analog of `StringSaturatedTwoCellConv`.
  * **Route.**  The sister lane `WalkingIdempotent/` already ships, zero-axiom, `idempotentThinness_ofNormalize`
    (full thinness from ANY boundary-determined normalizer `rep` + `normalize : cell ≈ rep cell`) and
    `normalizeFull` (the general-`n` boundary-determined normalizer, `fxIdempotentMonad_hasGeneralThinnessNormalizer`).
    The quadruple work is (a) a COUPLED boundary-determined normalizer at the shared `♭` (the analog of the string's
    shared-`G` snake, collapsed by thinness), and (b) the two idempotency rows.  This BYPASSES the length-rigidity
    residual entirely (no valley reconstruction), so it is materially cheaper than the raw string triple completeness
    and is the correct #2021 target.

Raw Lean 4 + Init; the pin is `cases` on the four `StringTwoCell` constructors with the width hypotheses
discharging the wrong-shape cases and `left ≠ coLeft` propagated into the words by `injection`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Colour separation — `F ≠ H` propagated into the two-letter boundary words -/

/-- ★ **`F·G ≠ H·G`** (comparable at `base ⟶ base`).  The lower-unit cod word `F·G` and the upper-counit dom word
`H·G` share their SECOND letter `G = right` but differ in their FIRST letter (`F = left` vs `H = coLeft`, distinct
generators).  Cancel the common right factor `G` (`composePathRightCancel`), reducing to `F ≠ H`
(`string_left_ne_coLeft`).  The two words are defeq to `composePath (singleton F/H) (singleton G)`, so the cancel
applies on the nose. -/
theorem stringFG_ne_stringHG : stringFG ≠ stringHG := by
  intro wordsEqual
  have wordsInComposeForm :
      composePath (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.left)
          (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.right)
        = composePath (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.coLeft)
          (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.right) := wordsEqual
  exact string_left_ne_coLeft (composePathRightCancel _ _ _ wordsInComposeForm)

/-- ★ **`G·H ≠ G·F`** (comparable at `tip ⟶ tip`).  The upper-unit cod word `G·H` and the lower-counit dom word
`G·F` share their FIRST letter `G = right` but differ in their SECOND letter (`H = coLeft` vs `F = left`).  Cancel the
common left factor `G` (`composePathLeftCancel`), reducing to `H ≠ F` — again `string_left_ne_coLeft` (symmetrized).
The two words are defeq to `composePath (singleton G) (singleton H/F)`. -/
theorem stringGH_ne_stringGF : stringGH ≠ stringGF := by
  intro wordsEqual
  have wordsInComposeForm :
      composePath (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.right)
          (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.coLeft)
        = composePath (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.right)
          (singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.left) := wordsEqual
  exact string_left_ne_coLeft (composePathLeftCancel _ wordsInComposeForm).symm

/-! ## The label-pinning crux — a cup's cod word is never a cap's dom word -/

/-- ★★ **The LABEL-PINNING crux — a string cup's cod word is NEVER a string cap's dom word.**  For any pair of
generating 2-cells `cupGen`, `capGen` between the SAME pair of mid-modes, if `cupGen` is a cup (its source word is
empty, `cupDom.length = 0`) and `capGen` is a cap (its target word is empty, `capCod.length = 0`), then the cup's
cod word `cupCod` is DISTINCT from the cap's dom word `capDom`.

The cups open `{F·G, G·H}` and the caps close `{G·F, H·G}`; the mode indices force the only comparable pairs to be
`F·G` vs `H·G` (both `base ⟶ base`) and `G·H` vs `G·F` (both `tip ⟶ tip`), each distinct by colour separation
(`stringFG_ne_stringHG` / `stringGH_ne_stringGF`).  The wrong-shape generators (a counit where a cup is required, a
unit where a cap is required) are excluded by the two width hypotheses.

This is the machine-checked "positions are pinned" fact: the mixed-colour cup·cap that the colour-blind width
classifier could route to the straighten arm can NEVER reconnect (that would demand `cupCod = capDom`, refuted here),
so a shared-leg cup·cap in the walking adjoint triple is forced same-colour — the r6 pin the r4/r5 rounds owed. -/
theorem stringCupCod_ne_capDom
    {midSource midTarget : AdjointTripleMode}
    {cupDom cupCod : ModalityPath adjointTripleGraph midSource midTarget}
    {capDom capCod : ModalityPath adjointTripleGraph midSource midTarget}
    (cupGen : StringTwoCell cupDom cupCod) (capGen : StringTwoCell capDom capCod)
    (cupIsCup : cupDom.length = 0) (capIsCap : capCod.length = 0) :
    cupCod ≠ capDom := by
  cases cupGen with
  | unitLower =>
      cases capGen with
      | unitLower => exact absurd capIsCap (by decide)
      | counitUpper => exact stringFG_ne_stringHG
  | unitUpper =>
      cases capGen with
      | unitUpper => exact absurd capIsCap (by decide)
      | counitLower => exact stringGH_ne_stringGF
  | counitLower => exact absurd cupIsCup (by decide)
  | counitUpper => exact absurd cupIsCup (by decide)

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the label-pinning crux is machine-checked.**  `stringCupCod_ne_capDom`: a string cup's cod
word (`F·G` or `G·H`) is NEVER a string cap's dom word (`G·F` or `H·G`), the two two-letter alphabets being disjoint
by colour separation (`stringFG_ne_stringHG` / `stringGH_ne_stringGF`, each `left ≠ coLeft` propagated into the
words).  This is the exact pin the r4/r5 rounds NAMED as owed (`stringSharedLegForcesSameColour`): the mixed-colour
cup·cap the colour-blind width classifier could route to the straighten arm can never reconnect, so a shared-leg
cup·cap is forced same-colour.  It replaces the adjunction's length-rigidity (`adjunctionPath_eq_of_length_eq`,
FALSE at the string) with constructive word bookkeeping — the r6 thesis, made a theorem.  `= true`. -/
def fxString_hasLabelPinningCrux : Bool := true

/-- **OPEN — the label pin does NOT flip completeness; the two producers stay a multi-round colour-aware port.**
`stringCupCod_ne_capDom` is the machine-checked HEART of the r6 word-bookkeeping thesis, and it discharges the exact
node the width-only classifier could not (`stringSharedLegForcesSameColour`).  But inhabiting the per-step
`StringCellDescentStepOracle` still requires re-deriving the whole colour-aware STRAIGHTEN assembly + COMMUTE
producer, and proving `StringCellValleyTraceEquiv` still requires the colour-aware valley reconstruction — both the
~92K-line `adjunctionModeSignature`-hardcoded valley apparatus re-derived with word bookkeeping, a genuinely
MULTI-ROUND arc.  That multi-round arc ran and closed: the flip came via the r45 determinacy brick, NOT via this
pin — `fxString_hasAdjointTripleCompleteness` (in `StringMatchingCompleteness`) is now `true` and
`decidableStringSaturatedConv_holds` is unconditional; this FromPin marker records only what the pin ITSELF
delivers and stays `false`.  The honest ledger at the time of this file (r6): SOUNDNESS DECIDED (r2), COMPLETENESS
then-open with the pin shipped and the exact remaining site named; the then-recommended next target was the
#2021 idempotent-quadruple pivot (thinness route via `idempotentThinness_ofNormalize`, see the file header spec),
which BYPASSES this residual entirely.  `= false`. -/
def fxString_hasAdjointTripleCompletenessFromPin : Bool := false

end FX1Poly.Polygraph
