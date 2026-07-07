import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence

/-! # ArcPureCapSpine — cupAtomCount zero detects the pure-cap regime (peel-first cap sort)

The pure-CAP mirror of `ArcPureCupSpine`.  Where the cup base case fires when a spine has no caps
left (`capAtomCount = 0`), the pure-cap sort peels caps from the FRONT — every cap reads two
existing boundary ports and cancels against the head (`spineArcHeadExtractionChained_ofCapArity`) —
and its regime predicate is the dual: a spine whose `cupAtomCount` is zero is PURE CAP, every atom
carrying cap arity `(2, 0)`.

  * `AllCapArity` — a structural predicate (not `List.Mem`-based, so the discharge stays
    `propext`-free): every atom in the spine has cap arity `(dom.length, cod.length) = (2, 0)`.
  * ★ `allCapArity_ofCupAtomCountZero` — `cupAtomCount atoms = 0` forces `AllCapArity atoms`.  A cup
    head would add one to the cup tally (contradiction); a cap head adds nothing, so the tail count
    is still zero and the induction carries.
  * `cupAtomCount_ofAllCapArity` — the converse: a pure-cap spine has zero cup tally.
  * `capAtomCount_ofAllCapArity` — a pure-cap spine's cap tally is its length (every position fires
    the cap guard).
  * `allCapArity_ofCons` — `propext`-free cons-inversion (a pure-cap tail), routed through the cup
    count.
  * `headCapArity` — the head of a pure-cap spine carries cap arity `(2, 0)`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The pure-cap predicate.**  Every atom in the spine carries cap arity `(dom.length,
cod.length) = (2, 0)`.  Structural (not `List.Mem`-based) so the peel-first recursion recurses on it
and the discharge stays `propext`-free. -/
inductive AllCapArity {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode} :
    List (SpineAtom signature sourceMode targetMode) → Prop
  | nil : AllCapArity []
  | cons {headAtom : SpineAtom signature sourceMode targetMode}
      {rest : List (SpineAtom signature sourceMode targetMode)}
      (hasCapDomArity : headAtom.generatorDom.length = 2)
      (hasCapCodArity : headAtom.generatorCod.length = 0)
      (restAllCap : AllCapArity rest) : AllCapArity (headAtom :: rest)

/-- ★ **`cupAtomCount` zero forces a pure-cap spine.**  At the walking adjunction every atom is a
cup or a cap; if the total cup tally is zero then no atom is a cup, so every atom has cap arity
`(2, 0)` — packaged as `AllCapArity`.  By induction on the spine: a cup head would contribute one to
the tally (refuting `= 0`), so the head is a cap and the tail still tallies zero. -/
theorem allCapArity_ofCupAtomCountZero
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    cupAtomCount atoms = 0 → AllCapArity atoms := by
  induction atoms with
  | nil => intro _; exact AllCapArity.nil
  | cons headAtom rest inductionHypothesis =>
      intro noCups
      have headCap : headAtom.generatorDom.length = 2 ∧ headAtom.generatorCod.length = 0 := by
        cases adjunctionSpineAtom_isCupOrCap headAtom with
        | inr capArity => exact capArity
        | inl cupArity =>
            exfalso
            have guardTrue :
                (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
              rw [cupArity.1, cupArity.2]
              rfl
            dsimp only [cupAtomCount] at noCups
            rw [if_pos guardTrue] at noCups
            exact Nat.noConfusion (Nat.add_comm 1 (cupAtomCount rest) ▸ noCups)
      have restNoCups : cupAtomCount rest = 0 := by
        have guardFalse :
            ¬ (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
          rw [headCap.1]
          exact Bool.noConfusion
        dsimp only [cupAtomCount] at noCups
        rw [if_neg guardFalse, Nat.zero_add] at noCups
        exact noCups
      exact AllCapArity.cons headCap.1 headCap.2 (inductionHypothesis restNoCups)

/-- **The converse of `allCapArity_ofCupAtomCountZero`.**  A pure-cap spine has zero cup tally:
every atom has cap arity `(2, 0)`, so its codomain length is `0`, not `2`, and the cup guard never
fires.  By induction on the `AllCapArity` witness. -/
theorem cupAtomCount_ofAllCapArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    AllCapArity atoms → cupAtomCount atoms = 0 := by
  intro allCap
  induction allCap with
  | nil => rfl
  | cons hasCapDomArity hasCapCodArity restAllCap restCupZero =>
      rename_i headAtom rest
      dsimp only [cupAtomCount]
      have guardFalse :
          ¬ (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
        rw [hasCapDomArity]
        exact Bool.noConfusion
      rw [if_neg guardFalse, Nat.zero_add]
      exact restCupZero

/-- **A pure-cap spine's cap tally is its length.**  Every atom has cap arity `(2, 0)`, so the cap
guard fires at every position and the fold counts one per atom.  By induction on the `AllCapArity`
witness. -/
theorem capAtomCount_ofAllCapArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    AllCapArity atoms → capAtomCount atoms = atoms.length := by
  intro allCap
  induction allCap with
  | nil => rfl
  | cons hasCapDomArity hasCapCodArity restAllCap restLengthEq =>
      rename_i headAtom rest
      have guardTrue :
          (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
        rw [hasCapDomArity, hasCapCodArity]
        rfl
      show (if (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) then 1 else 0)
          + capAtomCount rest = (headAtom :: rest).length
      rw [if_pos guardTrue, List.length_cons, restLengthEq]
      exact Nat.add_comm 1 rest.length

/-- The right summand of a `Nat` sum that vanishes is itself zero — a `noConfusion` peel, staying
`propext`-free where `Nat.eq_zero_of_add_eq_zero_left` / `Nat.succ_ne_zero` would leak. -/
private theorem addRightZero {leftSummand rightSummand : Nat}
    (sumZero : leftSummand + rightSummand = 0) : rightSummand = 0 := by
  cases rightSummand with
  | zero => rfl
  | succ predRight => exact Nat.noConfusion sumZero

/-- ★ **`AllCapArity` cons-inversion, `propext`-free.**  A pure-cap spine's tail is pure cap.  The
peel-first recursion peels a head cap and recurses on the tail, so it needs `AllCapArity rest` from
`AllCapArity (headAtom :: rest)`.  A direct `cases` on the head-indexed `AllCapArity` would leak
`propext` (partial match on an indexed inductive); instead route through the cup count — the head
contributes a non-negative summand, so the tail's cup tally is still zero (`addRightZero`) — and
rebuild via `allCapArity_ofCupAtomCountZero`. -/
theorem allCapArity_ofCons
    {overallSource overallTarget : adjunctionGraph.Mode}
    {headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (consPureCap : AllCapArity (headAtom :: rest)) : AllCapArity rest := by
  have consCupZero : cupAtomCount (headAtom :: rest) = 0 :=
    cupAtomCount_ofAllCapArity (headAtom :: rest) consPureCap
  have restCupZero : cupAtomCount rest = 0 := by
    dsimp only [cupAtomCount] at consCupZero
    exact addRightZero consCupZero
  exact allCapArity_ofCupAtomCountZero rest restCupZero

/-- ★ **A pure-cap head carries cap arity `(2, 0)`.**  Every walking-adjunction atom is a cup or a
cap (`adjunctionSpineAtom_isCupOrCap`); a cup head would contribute one to the cup tally
(`cupAtomCount_ofAllCapArity` forces zero), refuting `= 0`.  Routed through the cup count rather than
an indexed `cases` on `AllCapArity`, so it stays `propext`-free. -/
theorem headCapArity
    {overallSource overallTarget : adjunctionGraph.Mode}
    {headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (consPureCap : AllCapArity (headAtom :: rest)) :
    headAtom.generatorDom.length = 2 ∧ headAtom.generatorCod.length = 0 := by
  have consCupZero : cupAtomCount (headAtom :: rest) = 0 :=
    cupAtomCount_ofAllCapArity (headAtom :: rest) consPureCap
  cases adjunctionSpineAtom_isCupOrCap headAtom with
  | inr capArity => exact capArity
  | inl cupArity =>
      exfalso
      have guardTrue :
          (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
        rw [cupArity.1, cupArity.2]
        rfl
      dsimp only [cupAtomCount] at consCupZero
      rw [if_pos guardTrue] at consCupZero
      exact Nat.noConfusion (Nat.add_comm 1 (cupAtomCount rest) ▸ consCupZero)

/-! ## Honesty marker -/

/-- **Honesty marker — `cupAtomCount` zero detects the pure-cap regime (peel-first cap sort).**
`allCapArity_ofCupAtomCountZero`: at the walking adjunction, a spine with zero total cup tally
satisfies `AllCapArity` — every atom carries cap arity `(2, 0)`.  The converse
`cupAtomCount_ofAllCapArity`, the length reflection `capAtomCount_ofAllCapArity`, the `propext`-free
cons-inversion `allCapArity_ofCons`, and the head arity `headCapArity` complete the purity kit.  What
this marker does NOT claim: the peel-first cap sort itself (the assembly rung).  `= true`. -/
def fxMode_hasArcPureCapSpine : Bool := true

end FX1Poly.Polygraph
