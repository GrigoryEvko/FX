import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.BareConvFragmentDecision

/-! # mode-3 floor — the bare-`TwoCellConv` WORD-CODE COMPLETENESS frontier: `wordCode` is PROVABLY INCOMPLETE on
GENERAL (multi-generator) cells — machine-refuted by a two-generator Godement collision pair, the deepest honest
wall of the arc

`BareConvFragmentDecision` (r3) shipped `RawTwoCellExpr.wordCode` — the injective additive whisker-pattern code
`Σ_gen code(pattern gen)` (bijective base-2, digits `{1, 2}`) — and PROVED two things: (a) `wordCode` is a GENUINE
bare-conv invariant (`TwoCellConv.wordCode_eq`, surviving the interchange critical pair), and (b) on the
SINGLE-generator nil-whisker fragment `wordCode` is COMPLETE (`frameWord_twoCellConv_iff`: bare-conv ↔ word
equality, because there `wordCode = phi` is INJECTIVE — a size-1 multiset is its own sum).  r3 left the GENERAL
completeness untested: does `TwoCellConvFull a b` PLUS `wordCode a = wordCode b` force bare `TwoCellConv a b` on
MULTI-generator cells?

This file settles that exact question — NEGATIVELY, and mechanically.  The r4-PRIMARY completeness statement
`wordCode_complete` is FALSE: `wordCode` is a Parikh-style ADDITIVE shadow (`Σ_gen code(pattern gen)`), and while
`code` is injective PER pattern, the SUM over generators is symmetric and COLLIDES across distinct pattern
MULTISETS.  The single-generator success (r3) is exactly the degenerate `|multiset| = 1` case where the sum IS the
single code; with `≥ 2` generators the sum forgets the multiset.  So the honest completion is the deeper wall (a
valid r4 completion): `wordCode` — the single unbounded moment that beat every finite bounded-subsequence tuple on
the fragment (r1 / r2 / r3) — joins `whiskerSum` / `rSum` / `crossSum` / `nestedCrossSum` as machine-checked
INCOMPLETE on general cells, and it is the SHARPEST such refutation: since `code` is injective per pattern, NO
additive `Σ_gen φ(pattern)` word-code whatsoever decides general bare-conv.  The genuinely complete bare invariant
is strictly the per-generator pattern MULTISET (r2's structural §2), whose decision still owes the OPEN interchange
critical-pair coherence (Gratzer).  The recon+lit settlement names the mechanism: the two-generator Godement
product is a "floating bubble" (Forest, Rewriting in Gray categories) — precisely where the interchange-invariant
word-code stops being complete (Delpeuch–Vicary: complete only on the CONNECTED / single-component fragment).

## The separating pair (concrete, cast-free, both bare-IRREDUCIBLE)

Two units, Godement-composed, with ONE nil-left-whisker on the LEFT unit versus on the RIGHT unit:

  * `wordCodeCollisionLeft  = hcomp (whiskerLeft nil unit) unit`  (in explicit `vcomp`/whisker form)
  * `wordCodeCollisionRight = hcomp unit (whiskerLeft nil unit)`

Both share the boundary `adjunctionBaseIdentity ⇒ adjunctionLeftRightTwice` DEFINITIONALLY (every whisker is the
identity 1-cell, `composePath nil x = x` and `composePath LR nil = LR` reduce on the nose), so the pair is statable
with NO boundary cast.  Their per-generator whisker patterns are `{[R,L], [L]}` versus `{[R], [L,L]}` — DISTINCT
multisets, but with EQUAL additive code sum `code[R,L] + code[L] = 4 + 1 = 5 = 2 + 3 = code[R] + code[L,L]`.  Both
are `isInterchangeNormal` (bare-IRREDUCIBLE), so this is the strongest form: even among bare NORMAL forms `wordCode`
collides once there are `≥ 2` generators.

## What this file ships (each piece zero-axiom)

  ★ **`wordCodeCollisionLeft` / `wordCodeCollisionRight`** — the two-generator separating pair (explicit
    `vcomp`/whisker form of the Godement products), with `isInterchangeNormal = true` (bare-irreducible) and
    `generatorCount = 2` smokes.
  ★ **`wordCodeCollision_wordCode_eq`** — EQUAL `wordCode` (`5 = 5`, `rfl`).
  ★ **`wordCodeCollisionLeft_coCrossSum` / `wordCodeCollisionRight_coCrossSum` / `_coCrossSum_differs`** — DISTINCT
    `coCrossSum` (`1` vs `0`): the r2 bare-conv invariant `#(R-before-L)` separates them (in Left the nil-`L` lands
    UNDER the Godement-baked `R` on the SAME generator, an `R`-before-`L` crossing; in Right it lands on the OTHER
    generator, crossing-free — bare-conv cannot move an `L` across the generator boundary, that is whisker
    functoriality, which bare lacks).
  ★ **`wordCodeCollision_convFull`** — the pair IS `TwoCellConvFull` (cast-free: strip the single nil-`L` off each
    side via the homogeneous `whiskerLeftUnit`, threaded by `vcompCongr*` / `whisker*Congr` to the common hub
    `hcomp unit unit`).
  ★ **`wordCodeCollision_not_twoCellConv`** — the pair is NOT bare `TwoCellConv` (`coCrossSum` `1 ≠ 0` via
    `TwoCellConv.coCrossSum_eq`).
  ★★ **`wordCode_not_complete`** — the r4-PRIMARY completeness statement is REFUTED: there is NO
    `∀ a b, TwoCellConvFull a b → wordCode a = wordCode b → TwoCellConv a b`.  Hence
    `fxMode_hasBareConvWordCodeIncompleteProven := true`.

## What stays as-is — `fxMode_hasModeRelativeConvDecision` NOT flipped

`wordCode`-completeness is the route that WOULD have flipped the general bare decision; it is now machine-refuted,
so the flip is UNREACHABLE via any additive word-code.  `fxMode_hasModeRelativeConvDecision` (its terminal
disposition in `ModeRelativeMetatheory`) STAYS `false` — bare `TwoCellConv`'s decidability remains the GENUINELY
OPEN interchange critical-pair coherence (Gratzer), and the complete invariant is the per-generator pattern
MULTISET, not any single `Nat`.  r1 / r2 / r3 soundness and shipped statements are NOT weakened; the disposed
trace / nfCell carriers are NOT re-flipped; the saturated / faithful decisions are untouched.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (the
moments are constant-`Nat`-motive full-enum matches computing by `rfl`; `_coCrossSum_differs` is `rw` +
`Nat.noConfusion` on `1 = 0`; the full-conv is a cast-free `TwoCellConvFull` constructor chain; the refutation is a
direct counterexample application).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two-generator separating pair -/

/-- The single identity-1-cell LEFT whisker of the unit — `frameBaseNil ◁ unit`, in fully-applied `@`-form (the
whisker 1-cell must be pinned positionally; a bare `whiskerLeft (identityPath …)` under a declared codomain leaves
the 1-cell an unsolved index metavariable, exactly as `frameWord` documents).  Boundary `frameBaseNil ⇒
adjunctionLeftThenRight` (definitional). -/
abbrev unitWhiskeredLeftByNil :
    RawTwoCellExpr adjunctionModeSignature frameBaseNil adjunctionLeftThenRight :=
  @RawTwoCellExpr.whiskerLeft adjunctionModeSignature
    AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
    frameBaseNil frameBaseNil adjunctionLeftThenRight adjunctionUnitTwoCell

/-- The **LEFT** collision member `hcomp (frameBaseNil ◁ unit) unit`, in explicit `vcomp`/whisker form — the two
parallel units Godement-composed with the extra identity-1-cell LEFT whisker sitting on the LEFT unit.  Boundary
`adjunctionBaseIdentity ⇒ adjunctionLeftRightTwice` (definitional; all whiskers are the identity 1-cell).
Per-generator whisker patterns `{[R, L], [L]}`.  All whiskers `@`-pinned. -/
abbrev wordCodeCollisionLeft :
    RawTwoCellExpr adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice :=
  RawTwoCellExpr.vcomp
    (@RawTwoCellExpr.whiskerRight adjunctionModeSignature
      AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
      frameBaseNil adjunctionLeftThenRight frameBaseNil unitWhiskeredLeftByNil)
    (@RawTwoCellExpr.whiskerLeft adjunctionModeSignature
      AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
      adjunctionLeftThenRight frameBaseNil adjunctionLeftThenRight adjunctionUnitTwoCell)

/-- The **RIGHT** collision member `hcomp unit (frameBaseNil ◁ unit)`, in explicit `vcomp`/whisker form — the same
two units Godement-composed with the extra identity-1-cell LEFT whisker sitting on the RIGHT unit instead.  Same
boundary as `wordCodeCollisionLeft` (definitional).  Per-generator whisker patterns `{[R], [L, L]}`.  All whiskers
`@`-pinned. -/
abbrev wordCodeCollisionRight :
    RawTwoCellExpr adjunctionModeSignature adjunctionBaseIdentity adjunctionLeftRightTwice :=
  RawTwoCellExpr.vcomp
    (@RawTwoCellExpr.whiskerRight adjunctionModeSignature
      AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
      frameBaseNil adjunctionLeftThenRight frameBaseNil adjunctionUnitTwoCell)
    (@RawTwoCellExpr.whiskerLeft adjunctionModeSignature
      AdjunctionMode.base AdjunctionMode.base AdjunctionMode.base
      adjunctionLeftThenRight frameBaseNil adjunctionLeftThenRight unitWhiskeredLeftByNil)

/-- Both members are two-generator composites (`generatorCount = 2`) — the Godement product of two units. -/
theorem wordCodeCollisionLeft_generatorCount : wordCodeCollisionLeft.generatorCount = 2 := rfl

theorem wordCodeCollisionRight_generatorCount : wordCodeCollisionRight.generatorCount = 2 := rfl

/-- The LEFT member is bare-IRREDUCIBLE (`isInterchangeNormal = true`) — no `TwoCellStep` redex occurs. -/
theorem wordCodeCollisionLeft_isInterchangeNormal : wordCodeCollisionLeft.isInterchangeNormal = true := rfl

/-- The RIGHT member is bare-IRREDUCIBLE (`isInterchangeNormal = true`) — so the collision is between two genuine
bare NORMAL forms, not an artifact of unreduced redexes. -/
theorem wordCodeCollisionRight_isInterchangeNormal : wordCodeCollisionRight.isInterchangeNormal = true := rfl

/-! ## Equal word code — the additive-shadow collision -/

/-- ★ **The two members have EQUAL `wordCode` (`5 = 5`).**  Left scores `wordCode(whiskerRight nil (whiskerLeft nil
unit)) + wordCode(whiskerLeft LR unit) = 4 + 1 = 5`; Right scores `wordCode(whiskerRight nil unit) +
wordCode(whiskerLeft LR (whiskerLeft nil unit)) = 2 + 3 = 5`.  The per-generator code MULTISETS differ
(`{4, 1}` vs `{2, 3}`) but their SUMS coincide — the additive Parikh-style shadow collides across distinct
multisets.  `rfl` computes both through the `vcomp`/whisker recursion. -/
theorem wordCodeCollision_wordCode_eq :
    wordCodeCollisionLeft.wordCode = wordCodeCollisionRight.wordCode := rfl

/-! ## Distinct `coCrossSum` — the bare-conv separator -/

/-- The LEFT member scores `1` on `coCrossSum` (`#(R-before-L)`): its nil-`L` sits UNDER the Godement `R` on the
same generator, one `R`-before-`L` crossing. -/
theorem wordCodeCollisionLeft_coCrossSum : wordCodeCollisionLeft.coCrossSum = 1 := rfl

/-- The RIGHT member scores `0` on `coCrossSum`: its nil-`L` sits on the OTHER generator, crossing-free. -/
theorem wordCodeCollisionRight_coCrossSum : wordCodeCollisionRight.coCrossSum = 0 := rfl

/-- ★ The pair has DISTINCT `coCrossSum` (`1 ≠ 0`) — a genuine bare-conv invariant separates them. -/
theorem wordCodeCollision_coCrossSum_differs :
    wordCodeCollisionLeft.coCrossSum ≠ wordCodeCollisionRight.coCrossSum := by
  rw [wordCodeCollisionLeft_coCrossSum, wordCodeCollisionRight_coCrossSum]
  exact fun contradiction => Nat.noConfusion contradiction

/-! ## The pair IS `TwoCellConvFull` (cast-free, through the `hcomp unit unit` hub) -/

/-- ★ **The pair is `TwoCellConvFull`.**  Both sides strip their single identity-1-cell LEFT whisker to the common
hub `hcomp unit unit = vcomp (whiskerRight nil unit) (whiskerLeft LR unit)`: on the LEFT member the extra whisker
is inside the FIRST `vcomp` factor's body (stripped by `whiskerRightCongr nil (whiskerLeftUnit unit)`, threaded by
`vcompCongrLeft`); on the RIGHT member it is inside the SECOND factor's body (stripped by `whiskerLeftCongr LR
(whiskerLeftUnit unit)`, threaded by `vcompCongrRight`).  Cast-free — `whiskerLeftUnit` is the HOMOGENEOUS
functoriality law (`composePath nil dom = dom` definitionally), no `castBoundary`.  `trans` through the hub, `symm`
on the right leg. -/
theorem wordCodeCollision_convFull :
    TwoCellConvFull adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight :=
  TwoCellConvFull.trans
    (TwoCellConvFull.vcompCongrLeft
      (RawTwoCellExpr.whiskerLeft adjunctionLeftThenRight adjunctionUnitTwoCell)
      (TwoCellConvFull.whiskerRightCongr (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
        (TwoCellConvFull.whiskerLeftUnit adjunctionUnitTwoCell)))
    (TwoCellConvFull.symm
      (TwoCellConvFull.vcompCongrRight
        (RawTwoCellExpr.whiskerRight (identityPath (graph := adjunctionGraph) AdjunctionMode.base)
          adjunctionUnitTwoCell)
        (TwoCellConvFull.whiskerLeftCongr adjunctionLeftThenRight
          (TwoCellConvFull.whiskerLeftUnit adjunctionUnitTwoCell))))

/-! ## The pair is NOT bare `TwoCellConv` -/

/-- ★★ **The pair is NOT bare `TwoCellConv`.**  `coCrossSum` — a genuine bare-conv invariant
(`TwoCellConv.coCrossSum_eq`, preserved by every `TwoCellStep` including interchange) — scores them `1` versus `0`.
So two full-conv two-generator Godement composites with EQUAL `wordCode` are STILL not bare-convertible. -/
theorem wordCodeCollision_not_twoCellConv :
    ¬ TwoCellConv adjunctionModeSignature wordCodeCollisionLeft wordCodeCollisionRight :=
  fun conv => wordCodeCollision_coCrossSum_differs conv.coCrossSum_eq

/-! ## The refutation: `wordCode` is INCOMPLETE on general cells -/

/-- ★★ **`wordCode` completeness (the r4-PRIMARY) is FALSE.**  There is NO
`∀ a b, TwoCellConvFull a b → wordCode a = wordCode b → TwoCellConv a b` on general cells: the two-generator
Godement collision pair `wordCodeCollisionLeft` / `wordCodeCollisionRight` is `TwoCellConvFull`
(`wordCodeCollision_convFull`) with EQUAL `wordCode` (`wordCodeCollision_wordCode_eq`) yet is NOT bare
`TwoCellConv` (`wordCodeCollision_not_twoCellConv`).  So the general bare decision needs strictly more than the
interchange-invariant additive word-code — and since `code` is injective PER pattern, strictly more than ANY
additive `Σ_gen φ(pattern)` word-code.  The complete invariant is the per-generator pattern MULTISET (r2),
whose decision owes the OPEN Gratzer interchange coherence.  `wordCode`'s single-generator completeness
(`frameWord_twoCellConv_iff`) is exactly the degenerate `|multiset| = 1` case; this refutation is the general
`≥ 2`-generator failure. -/
theorem wordCode_not_complete :
    ¬ (∀ {sourceMode targetMode : adjunctionModeSignature.graph.Mode}
        {sourcePath targetPath : ModalityPath adjunctionModeSignature.graph sourceMode targetMode}
        (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
        TwoCellConvFull adjunctionModeSignature cellFirst cellSecond →
        cellFirst.wordCode = cellSecond.wordCode →
        TwoCellConv adjunctionModeSignature cellFirst cellSecond) :=
  fun completeness =>
    wordCodeCollision_not_twoCellConv
      (completeness wordCodeCollisionLeft wordCodeCollisionRight
        wordCodeCollision_convFull wordCodeCollision_wordCode_eq)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the bare-conv additive word-code `RawTwoCellExpr.wordCode` is PROVABLY INCOMPLETE on GENERAL
(multi-generator) cells (machine-checked), the deepest honest wall of the arc.**

Delivered (each zero-axiom): the two-generator Godement collision pair `wordCodeCollisionLeft` /
`wordCodeCollisionRight` (both `isInterchangeNormal`, `generatorCount = 2`, boundary
`adjunctionBaseIdentity ⇒ adjunctionLeftRightTwice` cast-free), with EQUAL `wordCode`
(`wordCodeCollision_wordCode_eq`, `5 = 5` — distinct code multisets `{4, 1}` / `{2, 3}`, equal sum), DISTINCT
`coCrossSum` (`wordCodeCollision_coCrossSum_differs`, `1 ≠ 0`), `TwoCellConvFull`
(`wordCodeCollision_convFull`, cast-free through the `hcomp unit unit` hub via the homogeneous `whiskerLeftUnit`),
and NOT bare `TwoCellConv` (`wordCodeCollision_not_twoCellConv`).  Hence the r4-PRIMARY completeness
`wordCode_not_complete` is REFUTED.

Reading: `wordCode` is a Parikh-style ADDITIVE shadow `Σ_gen code(pattern gen)`; `code` is injective PER pattern
(so on the single-generator fragment `wordCode = phi` is injective and COMPLETE — r3
`frameWord_twoCellConv_iff`), but the SUM over generators is symmetric and COLLIDES across distinct pattern
MULTISETS the moment `≥ 2` generators appear.  This is the SHARPEST refutation in the moment tower: `wordCode` was
the single unbounded moment that beat every finite bounded-subsequence tuple on the fragment, and it too is now
machine-checked incomplete on general cells — so NO additive `Σ_gen φ(pattern)` word-code decides general
bare-conv.  The genuinely complete bare invariant is strictly the per-generator pattern MULTISET (r2 §2), whose
decision still owes the OPEN interchange critical-pair coherence (Gratzer).  Literature: the two-generator
Godement product is a "floating bubble" (Forest), exactly where the interchange-invariant word-code stops being
complete (Delpeuch–Vicary: complete only on the CONNECTED / single-component fragment).

Untouched / not weakened: `fxMode_hasModeRelativeConvDecision` STAYS `false` (its terminal disposition in
`ModeRelativeMetatheory` — the general bare decision is UNREACHABLE via any additive word-code, and remains the
open Gratzer coherence); r1 / r2 / r3 soundness and shipped statements are NOT weakened; the disposed trace / nfCell
carriers are NOT re-flipped; the saturated / faithful decisions are untouched.  This flag records ONLY the
machine-checked general incompleteness of `wordCode`.  `= true`. -/
def fxMode_hasBareConvWordCodeIncompleteProven : Bool := true

end FX1Poly.Polygraph
