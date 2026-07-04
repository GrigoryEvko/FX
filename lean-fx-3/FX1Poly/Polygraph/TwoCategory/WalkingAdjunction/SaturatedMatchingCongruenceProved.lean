import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCanonicalization
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompRightUnconditional
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWhiskerLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWhiskerRightCongruence

/-! # mode-3 — the four-field matching compositionality, PROVED (MODE3-C closes)

The `MatchingSaturatedCongruence` bundle — the second named residual of the saturated
soundness reduction — is now a THEOREM: all four in-context compositionality fields are the
shipped headlines.

  * `vcompLeft` — `matchingOf_vcompLeft_congruence` (post-composition, the premise transports
    through the composite fold);
  * `vcompRight` — `matchingOf_vcompRight_congruence` (pre-composition, the Joyal–Street leg
    through the relative-run extract agreement, both mid-boundary legs);
  * `whiskerLeft` / `whiskerRight` — `matchingOf_whiskerLeft_congruence` /
    `matchingOf_whiskerRight_congruence` (boundary-padding compositionality).

  * ★ `matchingSaturatedCongruence_proved` — the bundle inhabitant;
  * ★ `saturatedConv_matchingOf_eq_ofGodementInvariant` — the saturated soundness with the
    congruence residual DISCHARGED: `matchingOf` is invariant under the complete
    `SaturatedTwoCellConv` modulo exactly ONE remaining named input, the union-find Godement
    block-commute independence (`fxMode_hasMatchingBlockCommuteProof = false`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The matching's saturated-congruence compositionality is PROVED.**  Each field is the
corresponding shipped congruence headline — the bundle stops being a hypothesis and becomes
a theorem. -/
theorem matchingSaturatedCongruence_proved : MatchingSaturatedCongruence where
  vcompLeft := @matchingOf_vcompLeft_congruence
  vcompRight := @matchingOf_vcompRight_congruence
  whiskerLeft := @matchingOf_whiskerLeft_congruence
  whiskerRight := @matchingOf_whiskerRight_congruence

/-- ★ **The saturated soundness, congruence residual discharged.**  `matchingOf` is invariant
under the complete `SaturatedTwoCellConv` given ONLY the union-find Godement independence —
the four congruence constructors now ride `matchingSaturatedCongruence_proved`. -/
theorem saturatedConv_matchingOf_eq_ofGodementInvariant
    (godementInvariant : ∀ {overallSource overallTarget : AdjunctionMode} (bottomCount : Nat)
        (state : WireState)
        {firstList secondList :
          List (SpineAtom adjunctionModeSignature overallSource overallTarget)},
        SpineGodementStep adjunctionModeSignature firstList secondList →
        extractAfterProcessing bottomCount state firstList
          = extractAfterProcessing bottomCount state secondList)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (conv : SaturatedTwoCellConv cellA cellB) : matchingOf cellA = matchingOf cellB :=
  saturatedConv_matchingOf_eq godementInvariant matchingSaturatedCongruence_proved conv

/-! ## Honesty marker -/

/-- **Honesty marker — the four-field `MatchingSaturatedCongruence` is PROVED.**  The second
named soundness residual of the saturated canonicalization is discharged; the saturated
soundness now reduces to exactly ONE named input, the union-find Godement block-commute
independence (`fxMode_hasMatchingBlockCommuteProof`, still `false`).  The completeness
reconstruction (`convOfMapEq`) remains the third residual.  `= true`. -/
def fxMode_hasMatchingSaturatedCongruence : Bool := true

end FX1Poly.Polygraph
