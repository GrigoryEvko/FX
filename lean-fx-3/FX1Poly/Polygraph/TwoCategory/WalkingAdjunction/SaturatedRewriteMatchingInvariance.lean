import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCongruenceProved

/-! # mode-3 — matching invariance along the saturated rewrite (the confluence question, resolved)

The saturated triangle-rewrite convergence question is now fully resolved, in two halves:

  * **NEGATIVE — full local confluence is FALSE.**  `SaturatedConvergence` ships the
    conditional Newman reduction (`saturatedTwoCellStep_isConfluent`) and the four
    triangle-layer critical-pair joins, but the `ofFree` layer inherits the free
    `interchange × whiskerRightVcomp` non-joining pair (Godement/Eckmann–Hilton: the two
    2×2-pasting decompositions are distinct terminal forms differing only in whiskering
    1-cells, which no rule rewrites — see the `FreeTwoCell/Confluence` module docstring).
    So `fxMode_hasSaturatedTwoCellConfluence = false` is CORRECT and the base-rule
    rewriting route cannot flip it.

  * **POSITIVE — the matching is the Church-Rosser-modulo-interchange surrogate.**  What
    confluence would have been USED for is separating inequivalent cells: two terms that
    rewrite to distinct normal forms must not be interconvertible.  The Temperley–Lieb
    matching delivers exactly that, without rewrite confluence: `matchingOf` is invariant
    along every saturated reduction (steps are sound for `SaturatedTwoCellConv`, and the
    canonicalization soundness — congruence residual discharged — evaluates conversions in
    the matching).  Hence matching-SEPARATED cells are never joinable.

Shipped here, each modulo the ONE remaining soundness input (the union-find Godement
block-commute independence, `fxMode_hasMatchingBlockCommuteProof = false`):

  * `saturatedReduces_matchingOf_eq_ofGodementInvariant` — `matchingOf` is invariant along
    the reflexive-transitive closure of `SaturatedTwoCellStep`;
  * `saturatedJoinable_matchingOf_eq_ofGodementInvariant` — joinable cells share their
    matching;
  * ★ `saturatedRewrite_notJoinable_ofMatchingSeparated` — the SEPARATION principle:
    distinct matchings ⟹ NOT joinable under the saturated rewrite.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **`matchingOf` is invariant along the saturated rewrite.**  Every many-step
`SaturatedTwoCellStep` reduction is a saturated convertibility
(`saturatedTwoCellReduces_toSaturatedConv`), and the canonicalization soundness with the
congruence residual discharged evaluates that convertibility in the matching. -/
theorem saturatedReduces_matchingOf_eq_ofGodementInvariant
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
    (reduction : Core.ReflTransClosure
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) =>
        SaturatedTwoCellStep a b)
      cellA cellB) : matchingOf cellA = matchingOf cellB :=
  saturatedConv_matchingOf_eq_ofGodementInvariant godementInvariant
    (saturatedTwoCellReduces_toSaturatedConv reduction)

/-- **Joinable cells share their matching.**  Both legs of a join are many-step reductions
to the common reduct, and `matchingOf` is invariant along each. -/
theorem saturatedJoinable_matchingOf_eq_ofGodementInvariant
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
    (joinable : Core.Joinable
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) =>
        SaturatedTwoCellStep a b)
      cellA cellB) : matchingOf cellA = matchingOf cellB := by
  obtain ⟨commonReduct, leftLeg, rightLeg⟩ := joinable
  exact (saturatedReduces_matchingOf_eq_ofGodementInvariant godementInvariant leftLeg).trans
    (saturatedReduces_matchingOf_eq_ofGodementInvariant godementInvariant rightLeg).symm

/-- ★ **The matching SEPARATION principle** — the usable replacement for the (false) full
local confluence: cells with DISTINCT matchings are never joinable under the saturated
rewrite.  This is what rewrite confluence would have been used for, delivered by the
Temperley–Lieb invariant instead of a normal-form argument. -/
theorem saturatedRewrite_notJoinable_ofMatchingSeparated
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
    (separated : matchingOf cellA ≠ matchingOf cellB) :
    ¬ Core.Joinable
      (fun (a b : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) =>
        SaturatedTwoCellStep a b)
      cellA cellB :=
  fun joinable =>
    separated (saturatedJoinable_matchingOf_eq_ofGodementInvariant godementInvariant joinable)

/-! ## Honesty marker -/

/-- **Honesty marker — the saturated confluence question is RESOLVED.**  Full local
confluence of `SaturatedTwoCellStep` is FALSE (the inherited free
`interchange × whiskerRightVcomp` Godement/Eckmann–Hilton pair; the conditional Newman
reduction and the narrative refutation live in `SaturatedConvergence`, whose
`fxMode_hasSaturatedTwoCellConfluence` correctly stays `false`).  The convergent content is
carried by the MATCHING instead: `matchingOf` is invariant along the saturated rewrite and
separates non-joinable cells, modulo exactly the union-find Godement block-commute residual
(`fxMode_hasMatchingBlockCommuteProof`).  `= true`. -/
def fxMode_hasSaturatedRewriteMatchingSeparation : Bool := true

end FX1Poly.Polygraph
