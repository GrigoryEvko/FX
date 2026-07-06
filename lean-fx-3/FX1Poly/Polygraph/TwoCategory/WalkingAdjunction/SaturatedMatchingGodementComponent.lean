import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingRenameComponent

/-! # SaturatedMatchingGodementComponent — the two-block commutation from the COMPONENT-level sigma

`SaturatedMatchingGodement` reduces the matching Godement soundness residual to a renaming witness
`MatchingGodementSwapRenameable`, whose `MatchingRenameRel` carries the ROOT-level `rootComm` that
the block transposition REFUTES (`not_matchingGodementSwapRenameable`).  `SaturatedMatchingRenameComponent`
shipped the corrected `MatchingRenameRelComponent` (component-level `sameComponentComm`) and its extract
invariance `extractDiagram_of_matchingRenameRelComponent`.  This brick re-wires the reduction onto the
corrected relation:

  * `MatchingGodementSwapRenameableComponent` — the two Godement run orders (redex `αUpper`-then-`β`,
    reduct `β`-then-`αUpper`, common `α` prefix, `βUpper` suffix, `rest` tail) are related by a
    COMPONENT-level renaming (`MatchingRenameRelComponent`);
  * ★ `matchingGodementCommute_of_swapRenameableComponent` — the component-level witness IMPLIES the
    two-block commutation core `MatchingGodementCommute`, with NOTHING else owed, by feeding
    `extractDiagram_of_matchingRenameRelComponent` — exactly as
    `matchingGodementCommute_of_swapRenameable` fed the root-level `extractDiagram_of_matchingRenameRel`.

`MatchingGodementCommute` is UNCHANGED, so the entire shipped downstream chain
(`matchingGodementInvariant_of_commute` → `saturatedConv_matchingOf_eq_of_commute` →
`saturatedMatchingCanonicalization_of`) accepts this reduction verbatim.  The soundness residual is
therefore now EXACTLY the COMPONENT-level sigma — the join-order-robust witness a genuine fresh-id
reordering bijection CAN satisfy, unlike the refuted root-level one.

Raw Lean 4 + Init; structural mirror of `matchingGodementCommute_of_swapRenameable`; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The COMPONENT-level matching Godement renaming residual.**  The two-block run orders — the redex
(`cellAlphaUpper` then `cellBeta`) and the reduct (`cellBeta` then `cellAlphaUpper`), with the common
`cellAlpha` prefix, `cellBetaUpper` suffix and `rest` tail — are related by a COMPONENT-level renaming
(`MatchingRenameRelComponent`).  The corrected form of `MatchingGodementSwapRenameable`: the refuted
root-level `rootComm` is replaced by `sameComponentComm`, so the join-order flip of the merged root no
longer blocks the witness — the fresh-id reordering bijection preserves the partition it needs to. -/
def MatchingGodementSwapRenameableComponent (signature : ModeSignature) : Prop :=
  ∀ {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (bottomCount : Nat) (state : WireState),
    ∃ sigma : Nat → Nat, MatchingRenameRelComponent bottomCount sigma
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)
      (processSpine
        (runMatchingCell (runMatchingCell (runMatchingCell
            (runMatchingCell state leftAcc (composePath gLow rightAcc) cellAlpha)
            (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBetaUpper) rest)

/-- ★ **The reduction, at the component level.**  The COMPONENT-level renaming witness
`MatchingGodementSwapRenameableComponent` IMPLIES the two-block commutation core `MatchingGodementCommute`
— the renaming witness between the two run orders feeds `extractDiagram_of_matchingRenameRelComponent` to
give the equal extract the core demands.  Identical shape to `matchingGodementCommute_of_swapRenameable`,
now through the join-order-robust component relation. -/
theorem matchingGodementCommute_of_swapRenameableComponent {signature : ModeSignature}
    (swapRenameable : MatchingGodementSwapRenameableComponent signature) :
    MatchingGodementCommute signature := by
  intro _ _ _ _ _ _ _ _ _ _ _ cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest
    bottomCount state
  obtain ⟨sigma, rel⟩ :=
    swapRenameable cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest bottomCount
      state
  exact extractDiagram_of_matchingRenameRelComponent bottomCount sigma _ _ rel

/-! ## Honesty marker -/

/-- **Honesty marker — the two-block commutation core is REDUCED to the COMPONENT-level sigma.**
`matchingGodementCommute_of_swapRenameableComponent` proves `MatchingGodementCommute` from
`MatchingGodementSwapRenameableComponent` (the two run orders related by the corrected component-level
renaming), feeding the shipped `extractDiagram_of_matchingRenameRelComponent`.  Since `MatchingGodementCommute`
is unchanged, the whole downstream chain (`matchingGodementInvariant_of_commute` →
`saturatedConv_matchingOf_eq_of_commute` → `saturatedMatchingCanonicalization_of`) accepts it verbatim, so
the matching Godement SOUNDNESS residual is now EXACTLY the join-order-robust component sigma.  What this
marker does NOT claim: CONSTRUCTING that sigma (the fresh-id reordering bijection between the two run
orders — the live soundness residual) nor the completeness `convOfMapEq`.  `= true`. -/
def fxMode_hasMatchingGodementCommuteFromComponent : Bool := true

end FX1Poly.Polygraph
