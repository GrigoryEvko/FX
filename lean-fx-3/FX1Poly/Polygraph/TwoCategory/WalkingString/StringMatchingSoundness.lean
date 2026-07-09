import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingCongruence

/-! # WalkingString — the FULL two-level soundness, UNCONDITIONAL (the cross-colour Godement discharged)

The full two-level soundness `stringSaturatedConv_matchingOf_eq` (StringMatchingModel) took two explicit premises:
the union-find Godement independence `godementInvariant` (the `ofFull` input) and the four-field congruence bundle
`StringMatchingSaturatedCongruence`.  `StringMatchingCongruence` discharged the second
(`stringMatchingSaturatedCongruence_proved`).  This file discharges the FIRST — the cross-colour Godement
transposition on the shared `G`-wire — and assembles the UNCONDITIONAL soundness.

## ★ Why the cross-colour Godement is NOT a coupling obstruction

The r1 residual named the crux: a colour-1 (`F ⊣ G`) cup/cap horizontally ADJACENT to a colour-2 (`G ⊣ H`)
cup/cap on the SHARED `G`-wire — the `triangleGlo` / `triangleGhi` overlap confluence.  The recon and the
literature (Joyal–Street planar-isotopy: interchange lets boxes on disjoint horizontal segments slide freely;
Temperley–Lieb / crossingless matchings: a FINITE adjoint presentation is decidable) locate the decision:

  * the union-find matching `matchingOf` is colour-BLIND — `stepAtom` reads only a generator's arity
    (`generatorDom.length`, `generatorCod.length` — `0 ⇒ 2` cup, `2 ⇒ 0` cap), NEVER its `F`/`G`/`H` label.
    The colours live ONLY in the boundary-fixed `pathLabels` (`ColouredDiagramType`), untouched by any
    convertibility;
  * so a colour-1 cup/cap adjacent to a colour-2 cup/cap is, at the union-find, exactly two cup/cap atoms — the
    SAME disjoint-window fragment the single-colour Godement already commuted.  There is NO cross-colour critical
    pair: the shared `G` couples the colours at the LABEL level (real, non-vacuous — the cross-level cell reads
    both), but is INVISIBLE to the connectivity model.

Concretely: the `ofFull` (interchange / free-strict-2-category) case is discharged for EVERY cup/cap-disciplined
cell — the walking adjoint triple's four generators are all cups/caps
(`cellHasCupCapGenerators_ofStringSignature`) — by the shipped signature-polymorphic capstone
`matchingOf_sound_ofCupCapCells_allBoundaries` (the union-find Godement independence, boundary-disciplined at
every source boundary, componentComm/disjoint-window content baked inside).  This is the SAME capstone that
closed the walking adjunction's own Godement (`saturatedConv_matchingOf_eq_ofBoundaryDiscipline`); the port to
three colour-blind generators is immediate.

## The assembly

  * `stringSaturatedConv_matchingOf_eq_ofBoundaryDiscipline` — the soundness with the `ofFull` case discharged by
    the cup/cap capstone (NO `godementInvariant` premise), the four congruences riding the proved bundle input;
  * ★ `stringSaturatedConv_matchingOf_eq_final` — the UNCONDITIONAL soundness (both residuals gone);
  * ★ `stringSaturatedConv_colouredMatchingOf_eq_final` — its two-level lift.

## Non-vacuity preserved

  * `stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi` — the discharged soundness IDENTIFIES the two distinct
    `G ⇒ G` snakes (colour 1 and colour 2) at the two-level matching, reproducing the shared-`G` coherence
    `stringSnakeGlo_conv_stringSnakeGhi` semantically;
  * `stringCrossLevel_colouredMatchingOf_ne_identityG` — the cross-level cell `G·F ⇒ G·H` is DISTINGUISHED from
    `id_G` (its two-level datum `[G,F] ⇒ [G,H]` differs from `id_G`'s `[G] ⇒ [G]`), so the flip does not collapse
    the cross-level structure.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The soundness, `ofFull` Godement leg discharged by the cup/cap capstone -/

/-- ★ **The soundness, re-gated on the cup/cap boundary discipline.**  `matchingOf` is invariant under the
COMPLETE `StringSaturatedTwoCellConv` given ONLY the four-field congruence bundle: the `ofFull` interchange /
Godement case is discharged by the PROVEN signature-polymorphic capstone
`matchingOf_sound_ofCupCapCells_allBoundaries` (every string cell is cup/cap-disciplined by
`cellHasCupCapGenerators_ofStringSignature`), the four triangles are on-the-nose (`matchingOf_stringTriangle*`,
`rfl`), the congruences consume the bundle, and `refl`/`symm`/`trans` chain.  The `godementInvariant` premise is
GONE — the cross-colour Godement on the shared `G` is subsumed by the colour-blind cup/cap discipline. -/
theorem stringSaturatedConv_matchingOf_eq_ofBoundaryDiscipline
    (congruence : StringMatchingSaturatedCongruence)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : StringSaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB := by
  induction conv with
  | ofFull convFull =>
      exact matchingOf_sound_ofCupCapCells_allBoundaries
        (cellHasCupCapGenerators_ofStringSignature _) convFull
  | triangleF => exact matchingOf_stringTriangleF
  | triangleGlo => exact matchingOf_stringTriangleGlo
  | triangleGhi => exact matchingOf_stringTriangleGhi
  | triangleH => exact matchingOf_stringTriangleH
  | vcompCongrLeft cellBeta _ inductionHypothesis => exact congruence.vcompLeft cellBeta inductionHypothesis
  | vcompCongrRight cellAlpha _ inductionHypothesis => exact congruence.vcompRight cellAlpha inductionHypothesis
  | whiskerLeftCongr oneCell _ inductionHypothesis => exact congruence.whiskerLeft oneCell inductionHypothesis
  | whiskerRightCongr oneCell _ inductionHypothesis => exact congruence.whiskerRight oneCell inductionHypothesis
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## ★ The unconditional soundness -/

/-- ★★ **The FULL two-level soundness — UNCONDITIONAL.**  `matchingOf` is invariant under the complete
`StringSaturatedTwoCellConv` with NO hypotheses: the congruence residual rides
`stringMatchingSaturatedCongruence_proved`, and the cross-colour Godement `ofFull` residual is discharged by the
cup/cap capstone.  BOTH named residuals of `stringSaturatedConv_matchingOf_eq` are gone. -/
theorem stringSaturatedConv_matchingOf_eq_final
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : StringSaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB :=
  stringSaturatedConv_matchingOf_eq_ofBoundaryDiscipline stringMatchingSaturatedCongruence_proved conv

/-- ★★ **The FULL two-level soundness lifts to `colouredMatchingOf` — UNCONDITIONAL.**  Saturated-convertible
cells have the SAME boundary matching (`stringSaturatedConv_matchingOf_eq_final`) AND identical boundary labels
(same source / target 1-cells), so their two-level matchings agree. -/
theorem stringSaturatedConv_colouredMatchingOf_eq_final
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (conv : StringSaturatedTwoCellConv cellA cellB) :
    colouredMatchingOf sourcePath targetPath cellA = colouredMatchingOf sourcePath targetPath cellB := by
  dsimp only [colouredMatchingOf]
  rw [stringSaturatedConv_matchingOf_eq_final conv]

/-! ## ★ Non-vacuity: the two G-snakes identified, the cross-level cell distinguished -/

/-- ★★ **The discharged soundness IDENTIFIES the two distinct `G ⇒ G` snakes.**  `stringSnakeGlo` (colour 1) and
`stringSnakeGhi` (colour 2) are syntactically distinct saturated snakes both collapsing to `id_G`; the
UNCONDITIONAL two-level soundness sends them to the SAME two-level matching, reproducing the shared-`G` coherence
`stringSnakeGlo_conv_stringSnakeGhi` semantically (not just as a posited relation).  So the flip is not vacuous:
the cross-level coupling on the shared `G` is genuinely sound. -/
theorem stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi :
    colouredMatchingOf (singletonModalityPath AdjointTripleModality.right)
        (singletonModalityPath AdjointTripleModality.right) stringSnakeGlo
      = colouredMatchingOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringSnakeGhi :=
  stringSaturatedConv_colouredMatchingOf_eq_final stringSnakeGlo_conv_stringSnakeGhi

/-- ★★ **The cross-level cell is DISTINGUISHED from `id_G`.**  The cross-level cell `G·F ⇒ G·H`
(`stringCrossLevelCell`, in neither single adjunction) has two-level datum `bottomLabels = [G,F]`,
`topLabels = [G,H]` and a two-boundary base matching, whereas `id_G` has `bottomLabels = [G]`, `topLabels = [G]`
and a single through-strand — so the unconditional soundness never equates them (they are not even parallel).
The flip discharges the cross-colour Godement WITHOUT collapsing the cross-level structure that makes the walking
adjoint triple more than two disjoint adjunctions. -/
theorem stringCrossLevel_colouredMatchingOf_ne_identityG :
    colouredMatchingOf stringGF stringGH stringCrossLevelCell
      ≠ colouredMatchingOf (singletonModalityPath AdjointTripleModality.right)
          (singletonModalityPath AdjointTripleModality.right) stringIdentityG := by
  decide

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the cross-colour Godement transposition is DISCHARGED, no coupling obstruction.**  The r1
cross-level residual — a colour-1 cup/cap adjacent to a colour-2 cup/cap on the SHARED `G`-wire — is NOT a
coupling obstruction: the union-find `matchingOf` is colour-BLIND (`stepAtom` reads arity only, never the
`F`/`G`/`H` label), so cross-colour adjacency is exactly the disjoint-window cup/cap fragment the single-colour
Godement already commuted.  The `ofFull` Godement leg is discharged for the whole (universally cup/cap-
disciplined) walking adjoint triple by the shipped capstone `matchingOf_sound_ofCupCapCells_allBoundaries`.  So
`fxString_hasCrossColourGodementObstruction = false`: there is NO exhibited colour-1/colour-2 pair whose Godement
transposition fails componentComm-order-independence — the shared `G` couples the colours only at the LABEL
level, invisible to the connectivity model.  `= false`. -/
def fxString_hasCrossColourGodementObstruction : Bool := false

/-- **★ ESTABLISHED — the FULL two-level soundness is UNCONDITIONAL.**  `stringSaturatedConv_matchingOf_eq_final`
proves `matchingOf` (and `stringSaturatedConv_colouredMatchingOf_eq_final` proves `colouredMatchingOf`) invariant
under the COMPLETE `StringSaturatedTwoCellConv` with NO hypotheses.  Both r1 residuals are discharged: the
four-field congruence via `stringMatchingSaturatedCongruence_proved` (the colour-blind whisker/vcomp cores ported
from the walking adjunction), and the cross-colour `ofFull` Godement via the cup/cap capstone.  Non-vacuous: the
two distinct `G`-snakes are identified (`stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi`) while the
cross-level cell stays distinguished from `id_G` (`stringCrossLevel_colouredMatchingOf_ne_identityG`).  `= true`. -/
def fxString_hasAdjointTripleSoundnessDischarged : Bool := true

end FX1Poly.Polygraph
