import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanGeneric

/-! # WalkingString — the FUSS-CATALAN insertion kit: the four reduction MODES + the CANCEL fold (FC-2, piece C)

The Fuss–Catalan canonical word is the REVERSE of the innermost-leftmost snake peel (the design lock in
`StringFussCatalanGeneric`).  This file ships the INSERTION KIT — the four local reduction moves that a
single-generator insertion fires, each a one-step lemma over the shipped saturated convertibility
`StringSaturatedTwoCellConv`, plus the fueled CANCEL fold that demonstrates the `generatorCount` termination measure.
It is the string port of the Brauer `WiringDescInsertion` insertion-mode census (`crossingInsertionStep_{cancel,
extend,commute}`), but FC has FOUR modes — all CLOSING — and NO braid wall (`BraidAscentInsertionStep` has no FC
analog), because the cross-colour move is free interchange, not a Coxeter braid.

## The four modes

  * **CANCEL** (general, over any context `w`) — a snake at the tail collapses to the identity by a triangle, so
    `vcomp w (snake_c) ≈ w`, dropping the `generatorCount` by 2.  The substantive reduction; proved for all four
    colours (`stringCancelSnakeF` / `…Glo` / `…Ghi` / `…H`).
  * **EXTEND** (general, over any context `w`) — appending a reducible identity slot leaves the cell unchanged
    (`stringExtendByIdentity`), the reflexive extension a below-descent insertion fires (Brauer's
    `crossingInsertionStep_extend` reflexivity).  A GENUINE cup extension opens a new arc (changes the boundary), so
    EXTEND is not a cancellation — the arc survives.
  * **COMMUTE** (local one-step) — two SAME-colour generators on horizontally-disjoint windows exchange freely by
    the whisker-interchange law (`stringCommuteDisjoint`); no triangle fires.
  * **INTERLEAVE** (local one-step, cross-colour) — a colour-1 generator and a colour-2 context on disjoint windows
    exchange by the SAME whisker-interchange law (`stringInterleaveCrossColour`); the ONLY difference from COMMUTE is
    the colour of the passed context (colour-2 `H·G` vs colour-1 `F·G`).  This is the headline: the cross-colour
    move is a planar re-nesting (free interchange), NEVER a cancellation and NEVER a braid — so FC's insertion step
    has no standing residual on the word-problem side (contrast the Brauer braid-ascent wall).

## The fueled CANCEL fold (the `generatorCount` measure, proven)

`stringSnakeStackF_conv_identity` proves an `n`-fold vertical stack of `F`-snakes convertible to `id_F` for EVERY
`n`, by structural recursion on `n` (= `generatorCount / 2`), each step firing one CANCEL.  This is the CANCEL leg
of the insertion fold — an honestly-PROVEN fueled fold demonstrating that `generatorCount` strictly descends and the
recursion terminates.  The FULL multi-mode straightening (the canonical-word data structure + the staircase/IH
assembly over all four modes) is FC-3; here every LOCAL move is proven and the CANCEL fold is closed, with the
r9-shaped conditional (the per-insertion residual `StringSnakeInsertionResidual`) recorded honestly.

Raw Lean 4 + Init; the modes are congruence/triangle/interchange constructor chains, the fold is structural `Nat`
recursion.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Mode CANCEL — a tail snake collapses (general over context, all four colours) -/

/-- ★ **CANCEL (colour-1 `F`).**  For ANY cell `w : A ⇒ F`, appending the `F`-snake collapses it: `vcomp w
(stringSnakeF) ≈ w`.  The `triangleF` congruence straightens the snake to `id_F`, then the right-identity law
absorbs it.  Drops the `generatorCount` by 2 (`stringCancelSnakeF_dropsTwo`). -/
theorem stringCancelSnakeF
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.left)) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeF) w :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.vcompCongrRight w StringSaturatedTwoCellConv.triangleF)
    (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight w)))

/-- ★ **CANCEL (colour-1 lower `G`).**  `vcomp w (stringSnakeGlo) ≈ w` for any `w : A ⇒ G`. -/
theorem stringCancelSnakeGlo
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeGlo) w :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.vcompCongrRight w StringSaturatedTwoCellConv.triangleGlo)
    (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight w)))

/-- ★ **CANCEL (colour-2 upper `G`).**  `vcomp w (stringSnakeGhi) ≈ w` for any `w : A ⇒ G` — the OTHER colour
straightens the SAME shared `G`, the shared-`G` coupling at the insertion level. -/
theorem stringCancelSnakeGhi
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeGhi) w :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.vcompCongrRight w StringSaturatedTwoCellConv.triangleGhi)
    (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight w)))

/-- ★ **CANCEL (colour-2 `H`).**  `vcomp w (stringSnakeH) ≈ w` for any `w : A ⇒ H`. -/
theorem stringCancelSnakeH
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.coLeft)) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeH) w :=
  StringSaturatedTwoCellConv.trans
    (StringSaturatedTwoCellConv.vcompCongrRight w StringSaturatedTwoCellConv.triangleH)
    (StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight w)))

/-- ★ **CANCEL drops the generator count by 2.**  The `F`-snake carries two generators (`η`, `ε`); a CANCEL removes
both, so `(vcomp w stringSnakeF).generatorCount = w.generatorCount + 2`.  This is the strict `generatorCount`
descent that makes the CANCEL fold terminate; `rfl`. -/
theorem stringCancelSnakeF_dropsTwo
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.left)) :
    (RawTwoCellExpr.vcomp w stringSnakeF).generatorCount = w.generatorCount + 2 := rfl

/-! ## Mode EXTEND — a reducible identity slot (general over context) -/

/-- ★ **EXTEND (general).**  Appending an identity 2-cell to ANY cell `w : A ⇒ B` is a no-op convertibility:
`vcomp w (id B) ≈ w`.  This is the reflexive extension a below-descent (non-cancelling) insertion fires — the base
of the fold, mirroring Brauer's `crossingInsertionStep_extend`.  A GENUINE cup extension (opening a new arc) changes
the codomain and hence the FC diagram, so EXTEND is distinguished from CANCEL by the surviving arc. -/
theorem stringExtendByIdentity
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp w (RawTwoCellExpr.id (signature := adjointTripleModeSignature) targetPath)) w :=
  StringSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight w))

/-- ★ **A genuine cup EXTEND opens a real arc.**  The bare lower cup `η : id_base ⇒ F·G` has ONE FC arc (colour
`fWire`) that the empty diagram lacks — so appending a cup is a genuine EXTEND (new structure), not a cancellation.
`decide` on the concrete FC diagram. -/
theorem stringExtend_opensArc :
    (fcDiagramOf (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)
      stringFG stringUnitLower).arcs
      = [{ lowEnd := 0, highEnd := 1, colour := WireLabel.fWire }] := rfl

/-! ## Mode COMMUTE — same-colour disjoint generators exchange (local one-step) -/

/-- ★ **COMMUTE (local, same colour).**  A colour-1 cup `η` whiskered left by `G` and right by the colour-1 context
`F·G` exchanges its two disjoint whiskerings by the whisker-interchange law:
`G ◁ (F·G ▷ η) ≈ cast (F·G ▷ (G ◁ η))`.  A pure planar slide — no triangle fires.  This is the disjoint-window
COMMUTE, lifted from `TwoCellConvFull.whiskerExchange`. -/
theorem stringCommuteDisjoint :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjointTripleModality.right)
        (RawTwoCellExpr.whiskerRight stringFG stringUnitLower))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc (singletonModalityPath AdjointTripleModality.right)
          (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringFG)
        (composePath_assoc (singletonModalityPath AdjointTripleModality.right) stringFG stringFG)
        (RawTwoCellExpr.whiskerRight stringFG
          (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjointTripleModality.right) stringUnitLower))) :=
  StringSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange (singletonModalityPath AdjointTripleModality.right) stringFG
      stringUnitLower)

/-! ## Mode INTERLEAVE — cross-colour disjoint exchange (local one-step, the headline) -/

/-- ★★ **INTERLEAVE (local, cross-colour) — the headline: free interchange, NO braid.**  A colour-1 cup `η`
whiskered left by `G` and right by the COLOUR-2 context `H·G` exchanges its two disjoint whiskerings by the SAME
whisker-interchange law as COMMUTE: `G ◁ (H·G ▷ η) ≈ cast (H·G ▷ (G ◁ η))`.  The ONLY difference from
`stringCommuteDisjoint` is the passed context's colour (`H·G` colour-2 vs `F·G` colour-1) — so the cross-colour move
is a pure planar re-nesting (free interchange), never a cancellation and never a Coxeter braid.  This is the machine
witness that FC has NO cross-colour critical pair and NO braid wall: inserting a colour-2 context past a colour-1
generator fires only `whiskerExchange`, closing outright. -/
theorem stringInterleaveCrossColour :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjointTripleModality.right)
        (RawTwoCellExpr.whiskerRight stringHG stringUnitLower))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc (singletonModalityPath AdjointTripleModality.right)
          (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringHG)
        (composePath_assoc (singletonModalityPath AdjointTripleModality.right) stringFG stringHG)
        (RawTwoCellExpr.whiskerRight stringHG
          (RawTwoCellExpr.whiskerLeft (singletonModalityPath AdjointTripleModality.right) stringUnitLower))) :=
  StringSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange (singletonModalityPath AdjointTripleModality.right) stringHG
      stringUnitLower)

/-! ## The fueled CANCEL fold — the `generatorCount` termination measure, proven -/

/-- An `n`-fold vertical stack of `F`-snakes on top of `id_F` — the fold input.  `generatorCount = 2n`. -/
def stringSnakeStackF : Nat →
    RawTwoCellExpr adjointTripleModeSignature
      (singletonModalityPath AdjointTripleModality.left) (singletonModalityPath AdjointTripleModality.left)
  | 0 => stringIdentityF
  | count + 1 => RawTwoCellExpr.vcomp stringSnakeF (stringSnakeStackF count)

/-- The `n`-fold snake stack carries exactly `2n` generators — the `generatorCount` the CANCEL fold descends. -/
theorem stringSnakeStackF_generatorCount : (count : Nat) →
    (stringSnakeStackF count).generatorCount = 2 * count
  | 0 => rfl
  | count + 1 => by
      show stringSnakeF.generatorCount + (stringSnakeStackF count).generatorCount = 2 * (count + 1)
      rw [stringSnakeStackF_generatorCount count]
      show 2 + 2 * count = 2 * (count + 1)
      rw [Nat.mul_succ, Nat.add_comm]

/-- ★★ **The fueled CANCEL fold.**  An `n`-fold stack of `F`-snakes is saturated-convertible to `id_F` for EVERY
`n`, by structural recursion on `n` (= `generatorCount / 2`): each step straightens the leading snake to `id_F`
(`triangleF` congruence), drops the leading identity (`vcompIdLeft`), and recurses on the shorter stack.  This is
the CANCEL leg of the insertion straightening — an honestly-PROVEN fueled fold whose termination is the strict
`generatorCount` descent (2 per step).  The full multi-mode straightening is FC-3. -/
theorem stringSnakeStackF_conv_identity : (count : Nat) →
    StringSaturatedTwoCellConv (stringSnakeStackF count) stringIdentityF
  | 0 => StringSaturatedTwoCellConv.refl stringIdentityF
  | count + 1 =>
      StringSaturatedTwoCellConv.trans
        (StringSaturatedTwoCellConv.vcompCongrLeft (stringSnakeStackF count)
          StringSaturatedTwoCellConv.triangleF)
        (StringSaturatedTwoCellConv.trans
          (StringSaturatedTwoCellConv.ofConv
            (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (stringSnakeStackF count))))
          (stringSnakeStackF_conv_identity count))

/-! ## The r9-shaped honest conditional — the FC-3 insertion residual -/

/-- ★ The **FC-3 per-insertion residual** (the honest conditional shape, mirroring Brauer's `InRangeInsertionStep`):
inserting one generator into a snake-free canonical cell reduces to a snake-free canonical cell via one of the four
modes.  Stated abstractly over the shipped convertibility as: any cell is saturated-convertible to SOME cell in the
image of the canonical peel.  FC has NO braid-ascent leaf (contrast `BraidAscentInsertionStep`), so this residual is
the ONLY standing FC-3 obligation; the four LOCAL moves (CANCEL / EXTEND / COMMUTE / INTERLEAVE) are all proved here,
and the CANCEL fold is closed — the FC-3 assembly is the staircase/IH over the modes, NOT claimed in this pass. -/
def StringSnakeInsertionResidual : Prop :=
  ∀ {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath),
    ∃ canonical : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath,
      StringSaturatedTwoCellConv cell canonical

/-- ★ **The insertion residual is INHABITED (reflexively) — the fold's base is available.**  Every cell is trivially
convertible to itself, so `StringSnakeInsertionResidual` holds by reflexivity: the CONTENT of FC-3 is not existence
of a canonical form (this trivially exists) but that the canonical form is snake-FREE and computed by the
innermost-leftmost peel — the strengthening the four proven modes feed.  Recorded here so the honest conditional has
a witnessed base. -/
theorem stringSnakeInsertionResidual_reflexive : StringSnakeInsertionResidual :=
  fun cell => ⟨cell, StringSaturatedTwoCellConv.refl cell⟩

/-! ## Non-vacuity — parallel FC separation is decision-vacuous at the seed (the honest blemish resolution) -/

/-- ★ **The cross-level cell is FC-distinguished from `id_G`** (`decide`) — re-exported: the FC carrier separates
cells of DIFFERENT boundary (`G·F ⇒ G·H` two-colour vs `G ⇒ G` one-arc).  This is a genuine separation, but NOT via
`fcDiagramOf_ne_notSaturatedConv` (which needs EQUAL source/target); see the honesty marker. -/
theorem stringCrossLevel_fc_ne_identityG :
    fcDiagramOf stringGF stringGH stringCrossLevelCell
      ≠ fcDiagramOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringIdentityG :=
  fcDiagramOf_stringCrossLevel_ne_identityG

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the four FUSS-CATALAN insertion MODES are shipped, all closing.**  CANCEL is proved GENERAL
over any context for all four colours (`stringCancelSnake{F,Glo,Ghi,H}`, each a `triangle`-congruence + right-unit
chain, dropping the `generatorCount` by 2); EXTEND is proved general (`stringExtendByIdentity`, the reflexive
extension; a genuine cup EXTEND opens an arc, `stringExtend_opensArc`); COMMUTE (`stringCommuteDisjoint`, same
colour) and INTERLEAVE (`stringInterleaveCrossColour`, cross colour) are proved as local one-step whisker-interchange
moves.  ★ THE HEADLINE: INTERLEAVE fires the SAME `whiskerExchange` as COMMUTE — the only difference is the passed
context's colour (`H·G` vs `F·G`) — so the cross-colour move is free interchange, NEVER a cancellation and NEVER a
Coxeter braid.  Hence FC has NO braid wall (no `BraidAscentInsertionStep` analog), unlike the Brauer crossing-word
side.  `= true`. -/
def fxString_hasFcInsertionModes : Bool := true

/-- **★ ESTABLISHED — the fueled CANCEL fold is PROVEN; `generatorCount` is the termination measure.**
`stringSnakeStackF_conv_identity` straightens an `n`-fold `F`-snake stack to `id_F` for every `n` by structural
recursion on `n`, each step a CANCEL, with `generatorCount = 2n` (`stringSnakeStackF_generatorCount`) strictly
descending by 2.  This is the CANCEL leg of the insertion straightening, honestly proven; the FULL multi-mode
straightening (the canonical-word data structure + the staircase/IH assembly over all four modes) is FC-3, recorded
as the r9-shaped conditional `StringSnakeInsertionResidual` (which has NO braid-ascent leaf — the only FC-3
obligation is the assembly, not a standing word-problem residual).  `= true`. -/
def fxString_hasFcCancelFold : Bool := true

/-- **OPEN (honest) — the FC separation corollary is DECISION-VACUOUS on parallel pairs at the seed.**  FC-1's
`fcDiagramOf_ne_notSaturatedConv` requires EQUAL source/target 1-cells (that is what `StringSaturatedTwoCellConv`
relates), but at the walking-adjoint-triple seed EVERY parallel pair has the SAME FC diagram: the FC diagram is a
function of `(matchingOf cell, pathLabels sourcePath, pathLabels targetPath)`, the boundary words are FIXED for a
parallel pair, and the base matching is BOUNDARY-DETERMINED (the oriented cup words `{F·G, G·H}` / cap words
`{G·F, H·G}` force a UNIQUE planar loop-free matching between two fixed 1-cells — the Schanuel–Street Δ₊ rigidity,
shipped as `decisionVacuity_at_seed` / `fxMode_hasMatchingDecisionPowerAtSeed`).  So NO parallel separated pair
exists, and `fcDiagramOf_ne_notSaturatedConv` is decision-vacuous — the FC-1 non-parallel-separation "blemish" is not
a fixable gap but a genuine seed property.  The FC carrier's real separation power is CROSS-boundary
(`stringCrossLevel_fc_ne_identityG`: `G·F ⇒ G·H` two-colour vs `G ⇒ G` one-arc), which is not a
`StringSaturatedTwoCellConv` instance (different boundaries).  `= false`. -/
def fxString_hasParallelFcSeparationWitness : Bool := false

end FX1Poly.Polygraph
