import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyProgress

/-! # SpineValleyBlockSplit — the Piece-I block extractor: a `Bool`-tag valley IS a typed cap-block ++ cup-block

The cell-level Piece I driver (`SpineValleyCellDriver`) reaches a valley classified by the `Bool` fold
`isCapThenCupValley SpineAtom.isCupAtom cell.spine = true`.  The whole Piece-II tail
(`valleysWithEqualMatching_spineTraceEquiv`) consumes the valley in the STRUCTURED form `capBlock ++ cupBlock`
with the two typed arity predicates `AllCapArity capBlock` and `AllCupArity cupBlock`.  This file is the exact
BRIDGE between the two presentations — the "block extractor" the Piece-I route names:

  * ★ `spineValley_blockSplit` — a spine satisfying the `Bool` valley predicate splits CONCRETELY as
    `capBlock ++ cupBlock` with `AllCapArity capBlock` (each atom cap arity `(2, 0)`) and `AllCupArity cupBlock`
    (each atom cup arity `(0, 2)`).  Structural induction following `isCapThenCupValley`'s own recursion: walk the
    leading caps, and at the first cup the tail-is-all-cups check (`allCups`) yields the cup block.

The tag→arity coincidence at the walking adjunction is exact: `adjunctionSpineAtom_isCupOrCap` makes every atom a
cup `(0, 2)` or a cap `(2, 0)`, and `SpineAtom.isCupAtom` (a cup iff `generatorDom.length = 0`) reads exactly that
dichotomy — so the `Bool`-tag valley predicate and the arity predicates coincide with NO semantic gap.

Raw Lean 4 + Init; two arity read-offs (`cupArity_of_isCupAtom_true` / `capArity_of_isCupAtom_false`), the
all-cups tail bridge (`allCupArity_of_allCups`), and the main structural split.  `propext`/`Quot.sound`/
`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Tag → arity read-offs at the walking adjunction -/

/-- A `SpineAtom.isCupAtom = true` atom carries cup arity `(0, 2)`.  `isCupAtom` is `true` iff
`generatorDom.length = 0`; at the adjunction `adjunctionSpineAtom_isCupOrCap` forces such an atom into the cup
branch (the cap branch has `generatorDom.length = 2`). -/
theorem cupArity_of_isCupAtom_true
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCup : SpineAtom.isCupAtom atom = true) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have isCapFalse : SpineAtom.isCupAtom atom = false := by
        dsimp only [SpineAtom.isCupAtom]
        rw [capArity.1]
      rw [isCapFalse] at isCup
      exact Bool.noConfusion isCup

/-- A `SpineAtom.isCupAtom = false` atom carries cap arity `(2, 0)`.  Dual of the cup read-off: `isCupAtom` is
`false` iff `generatorDom.length ≠ 0`, and `adjunctionSpineAtom_isCupOrCap` forces the cap branch `(2, 0)`. -/
theorem capArity_of_isCupAtom_false
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (isCap : SpineAtom.isCupAtom atom = false) :
    atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 0 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inr capArity => exact capArity
  | inl cupArity =>
      exfalso
      have isCupTrue : SpineAtom.isCupAtom atom = true := by
        dsimp only [SpineAtom.isCupAtom]
        rw [cupArity.1]
      rw [isCupTrue] at isCap
      exact Bool.noConfusion isCap

/-! ## The all-cups tail bridge -/

/-- `allCups SpineAtom.isCupAtom xs = true` — every tail atom is a cup by the `Bool` fold — upgrades to the typed
`AllCupArity xs` (every atom cup arity `(0, 2)`).  Structural induction splitting the `&&` by hand (no
`Bool.and_eq_true` iff, keeping the discharge propext-free). -/
theorem allCupArity_of_allCups
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (xs : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    allCups SpineAtom.isCupAtom xs = true → AllCupArity xs
  | [], _ => AllCupArity.nil
  | atom :: rest, allCupsTrue => by
      dsimp only [allCups] at allCupsTrue
      cases isCupHead : SpineAtom.isCupAtom atom with
      | false =>
          rw [isCupHead] at allCupsTrue
          exact Bool.noConfusion allCupsTrue
      | true =>
          rw [isCupHead] at allCupsTrue
          obtain ⟨cupDom, cupCod⟩ := cupArity_of_isCupAtom_true atom isCupHead
          exact AllCupArity.cons cupDom cupCod (allCupArity_of_allCups rest allCupsTrue)

/-! ## The block extractor -/

/-- ★ **The Piece-I block extractor.**  A spine that the `Bool` fold classifies as a valley
(`isCapThenCupValley SpineAtom.isCupAtom spine = true`) splits CONCRETELY as `capBlock ++ cupBlock` with typed
arity: `AllCapArity capBlock` (leading caps) and `AllCupArity cupBlock` (the cup run from the first cup on).  This
is the presentation the whole Piece-II tail consumes.  Structural induction following the valley predicate's own
recursion: at a cap head, recurse and prepend the cap to the cap block; at a cup head, the valley check demands
the tail be all cups, so the whole cons is the cup block and the cap block is empty. -/
theorem spineValley_blockSplit
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    isCapThenCupValley SpineAtom.isCupAtom spine = true →
    ∃ (capBlock cupBlock : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      spine = capBlock ++ cupBlock ∧ AllCapArity capBlock ∧ AllCupArity cupBlock
  | [], _ => ⟨[], [], rfl, AllCapArity.nil, AllCupArity.nil⟩
  | atom :: rest, isValley => by
      dsimp only [isCapThenCupValley] at isValley
      cases isCupHead : SpineAtom.isCupAtom atom with
      | true =>
          rw [isCupHead] at isValley
          -- `isValley : allCups SpineAtom.isCupAtom rest = true`; the whole cons is the cup block.
          obtain ⟨cupDom, cupCod⟩ := cupArity_of_isCupAtom_true atom isCupHead
          exact ⟨[], atom :: rest, rfl, AllCapArity.nil,
            AllCupArity.cons cupDom cupCod (allCupArity_of_allCups rest isValley)⟩
      | false =>
          rw [isCupHead] at isValley
          -- `isValley : isCapThenCupValley SpineAtom.isCupAtom rest = true`; recurse, prepend the cap.
          obtain ⟨capBlock, cupBlock, splitEq, capArity, cupArity⟩ :=
            spineValley_blockSplit rest isValley
          obtain ⟨capDom, capCod⟩ := capArity_of_isCupAtom_false atom isCupHead
          refine ⟨atom :: capBlock, cupBlock, ?_, AllCapArity.cons capDom capCod capArity, cupArity⟩
          rw [splitEq]
          rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the Piece-I block extractor is SHIPPED, unconditional, zero-axiom.**
`spineValley_blockSplit` converts the cell driver's `Bool`-tag valley predicate
(`isCapThenCupValley SpineAtom.isCupAtom spine = true`) into the STRUCTURED `capBlock ++ cupBlock` form with typed
arity (`AllCapArity` / `AllCupArity`) that the whole Piece-II tail (`valleysWithEqualMatching_spineTraceEquiv`)
consumes — the tag→arity coincidence is exact at the walking adjunction (`adjunctionSpineAtom_isCupOrCap`).

  What this marker does NOT itself close: the width-telescoping length-determinacy (`capBlock`/`cupBlock` lengths
  agree from equal matching, needs `0 < sourcePath.length`) and the positivity dispatch for degenerate valleys
  (empty source / all-consuming cap block) — the remaining rungs of the cell-level `CellValleyTraceEquiv`.  No gate
  flag is flipped.  `= true`. -/
def fxMode_hasSpineValleyBlockSplit : Bool := true

end FX1Poly.Polygraph
