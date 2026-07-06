import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence

/-! # ArcPureCupSpine — capAtomCount zero detects the pure-cup regime (cap-first route, base-case entry)

The cap-first reconstruction route (#2168) peels caps preferentially — each cap cancels
cleanly against the head (`arcCapHeadFolded_extractArc_cancel`, the injective seed read-off) —
and reaches its BASE CASE exactly when the spine has no caps left.  This brick is the entry
predicate for that base case: at the walking adjunction, where every generator is a cup
(`0 ⇒ 2`) or a cap (`2 ⇒ 0`) (`adjunctionSpineAtom_isCupOrCap`), a spine whose `capAtomCount`
is zero is PURE CUP — every atom carries cup arity.

  * `AllCupArity` — a structural predicate: every atom in the spine has cup arity `(0, 2)`.
    Stated inductively (not through `List.Mem`) so the cap-first base case can recurse on it
    directly, and so the discharge stays `propext`-free (a `List.Mem` cons-index match leaks).
  * ★ `allCupArity_ofCapAtomCountZero` — `capAtomCount atoms = 0` forces `AllCupArity atoms`.
    A cap head would add one to the tally (contradiction); a cup head adds nothing, so the tail
    count is still zero and the induction carries.

The base case's own content — two pure-cup spines with equal arc structure are cup-interchange
(Godement) equivalent — is the next rung; this brick only isolates the regime.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The pure-cup predicate.**  Every atom in the spine carries cup arity `(dom.length,
cod.length) = (0, 2)`.  Structural (not `List.Mem`-based) so the cap-first base case recurses on
it and the discharge stays `propext`-free. -/
inductive AllCupArity {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → Prop
  | nil : AllCupArity []
  | cons {headAtom : SpineAtom signature sourceMode targetMode}
      {rest : List (SpineAtom signature sourceMode targetMode)}
      (hasCupDomArity : headAtom.generatorDom.length = 0)
      (hasCupCodArity : headAtom.generatorCod.length = 2)
      (restAllCup : AllCupArity rest) : AllCupArity (headAtom :: rest)

/-- ★ **`capAtomCount` zero forces a pure-cup spine.**  At the walking adjunction every atom is
a cup or a cap; if the total cap tally is zero then no atom is a cap, so every atom has cup
arity `(0, 2)` — packaged as `AllCupArity`.  By induction on the spine: a cap head would
contribute one to the tally (refuting `= 0`), so the head is a cup and the tail still tallies
zero. -/
theorem allCupArity_ofCapAtomCountZero
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    capAtomCount atoms = 0 → AllCupArity atoms := by
  induction atoms with
  | nil => intro _; exact AllCupArity.nil
  | cons headAtom rest inductionHypothesis =>
      intro noCaps
      have headCup : headAtom.generatorDom.length = 0 ∧ headAtom.generatorCod.length = 2 := by
        cases adjunctionSpineAtom_isCupOrCap headAtom with
        | inl cupArity => exact cupArity
        | inr capArity =>
            exfalso
            have guardTrue :
                (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
              rw [capArity.1, capArity.2]
              rfl
            dsimp only [capAtomCount] at noCaps
            rw [if_pos guardTrue] at noCaps
            exact Nat.noConfusion (Nat.add_comm 1 (capAtomCount rest) ▸ noCaps)
      have restNoCaps : capAtomCount rest = 0 := by
        have guardFalse :
            ¬ (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
          rw [headCup.1]
          exact Bool.noConfusion
        dsimp only [capAtomCount] at noCaps
        rw [if_neg guardFalse, Nat.zero_add] at noCaps
        exact noCaps
      exact AllCupArity.cons headCup.1 headCup.2 (inductionHypothesis restNoCaps)

/-! ## Honesty marker -/

/-- **Honesty marker — `capAtomCount` zero detects the pure-cup regime (cap-first route, base-case
entry).**  `allCupArity_ofCapAtomCountZero`: at the walking adjunction, a spine with zero total
cap tally satisfies `AllCupArity` — every atom carries cup arity `(0, 2)`.  What this marker does
NOT claim: the base case's content (equal-arc pure-cup spines are cup-interchange equivalent) nor
the cap-first recursion itself.  `= true`. -/
def fxMode_hasArcPureCupSpine : Bool := true

end FX1Poly.Polygraph
