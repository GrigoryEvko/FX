import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyRedexStep
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # mode-3 keystone — Piece I COMMUTE producer: the flat located swap IS the whole step

`SpineValleyRedexStep` reduced the oracle's COMMUTE branch to producing a `(next, stepConv)` pair, where
`stepConv : SaturatedTwoCellConv cell next` and `next.spine` is `cell.spine` with the located cup·cap pair
transposed to a slot-preserving cap·cup.  The prior note flagged the `stepConv` as needing the disjoint-window
swap lifted to the boundary-PATH level (a Godement `saturatedGodementExchange` conversion over the transposed
readback chain).  This file shows that is UNNECESSARY: because the descent is valued in `SaturatedTwoCellConv`,
and `SaturatedTwoCellConv.ofSpineTraceEquiv` lifts ANY trace equivalence of spines unconditionally, the FLAT
located `SpineAtomSwap` — the boundary-LENGTH-level swap the shipped `adjunctionSpineAtomSwap_of_disjointWindows`
already produces — suffices for the whole `stepConv`.  No Godement band-refactor, no path-level chain surgery for
the CONVERSION.

  * ★ **`spineTraceEquiv_prependAtoms`** — a whole atom PREFIX passes through trace equivalence, by folding the
    shipped head congruence `SpineTraceEquiv.consCongr` over the prefix list (structural recursion, `++` on a
    `cons` is `rfl`).  This is the located-behind-a-prefix generalization of the head swap.
  * ★ **`commutePrefixSwapCellLift`** — two cells sharing an atom prefix, whose remaining spines are related by a
    flat `SpineAtomSwap`, are `SaturatedTwoCellConv`: the swap is a Godement spine step (`toGodementStep`), hence
    a trace equivalence (`ofStep`), prefixed (`spineTraceEquiv_prependAtoms`) and lifted (`ofSpineTraceEquiv`).
    The `commuteAtomSwapCellLift` of `SpineValleyCellLift` is the empty-prefix instance; this is the arbitrary-
    depth COMMUTE `stepConv`, from the flat swap alone.
  * ★ **`cellDescentResult_ofCommutePrefixSwap`** — the COMMUTE `CellDescentResult` builder from the FLAT swap:
    given `next` with the transposed spine and the flat located `SpineAtomSwap (cup :: cap :: rest)
    (capMoved :: cupMoved :: rest)`, package the step (the `stepConv` via `commutePrefixSwapCellLift`, the
    `disorderDrops` via `spineDisorder_swap_lt` inside `cellDescentResult_ofCommuteStep`).  So the oracle's
    COMMUTE branch is reduced to EXACTLY: exhibit `next` (a cell with the transposed spine) and the flat located
    `SpineAtomSwap`.

## What this does NOT close (gates stay `false`)

The COMMUTE branch still owes the two INPUTS this builder consumes:

  * `next` — a cell whose spine is `cell`'s with the located pair transposed.  Constructing it needs the
    cell→chain realization (`RealizedSpineChain` for `cell`, split at the prefix, the middle pair inverted and
    re-consed swapped, read back by `chainToCell` — the boundary-PATH-level chain surgery), which threads the
    intermediate anchor path through `composePath_assoc`.  This file removes the need to build a path-level
    Godement conversion, NOT the need to build `next` itself;
  * the flat `SpineAtomSwap` from the classifier's `disjointWindows` verdict — deriving the `windowGap`
    factorization + the right-of/left-of sign from `natWindowDistance ≥ 2`, plus the raw spine's boundary
    chainedness at the located split, to feed `adjunctionSpineAtomSwap_of_disjointWindows`.

So `CellDescentStepOracle` stays UN-inhabited; `MatchingReductsShareSpineTrace`, `convOfMapEq`, and the fib-3
gate flags stay `false`.  This file makes the COMMUTE `stepConv` cheap (flat swap → whole conversion) and
isolates the COMMUTE residual to `next`-construction + flat-swap-derivation.

Raw Lean 4 + Init; the prefix congruence is structural recursion folding `consCongr`, the lift is
`ofSpineTraceEquiv ∘ prepend ∘ ofStep ∘ toGodementStep`, the builder chains into `cellDescentResult_ofCommuteStep`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

universe u

namespace FX1Poly.Polygraph

/-! ## A whole atom prefix passes through trace equivalence -/

/-- ★ **A whole atom prefix passes through trace equivalence.**  Folding the shipped head congruence
`SpineTraceEquiv.consCongr` over the prefix list: the empty prefix is the identity, a cons prefixes one atom by
`consCongr` onto the recursive prefixing of the tail (`(atom :: tail) ++ list = atom :: (tail ++ list)` is `rfl`,
so no cast).  This is the located-behind-a-prefix generalization the arbitrary-depth COMMUTE step needs. -/
theorem spineTraceEquiv_prependAtoms {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    ∀ prefixCells : List (SpineAtom signature overallSource overallTarget),
      SpineTraceEquiv signature (prefixCells ++ firstList) (prefixCells ++ secondList)
  | [] => equiv
  | atom :: tail => SpineTraceEquiv.consCongr atom (spineTraceEquiv_prependAtoms equiv tail)

/-! ## The flat located swap is the whole COMMUTE conversion -/

/-- ★ **The prefixed spine swap lifts to a cell conversion.**  Two cells sharing an atom prefix whose remaining
spines are related by a flat `SpineAtomSwap` are `SaturatedTwoCellConv`: the swap is a Godement spine step
(`SpineAtomSwap.toGodementStep`), hence a single trace equivalence (`SpineTraceEquiv.ofStep`), prefixed by the
shared atoms (`spineTraceEquiv_prependAtoms`) and lifted into the saturated relation
(`SaturatedTwoCellConv.ofSpineTraceEquiv`).  `commuteAtomSwapCellLift` (empty prefix) is the head instance; this
is the located-at-arbitrary-depth COMMUTE `stepConv`, built from the FLAT boundary-length swap ALONE — no
boundary-path Godement conversion. -/
theorem commutePrefixSwapCellLift {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (prefixCells : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {pairFirst pairSecond : List (SpineAtom adjunctionModeSignature sourceMode targetMode)}
    (firstSpine : cellFirst.spine = prefixCells ++ pairFirst)
    (secondSpine : cellSecond.spine = prefixCells ++ pairSecond)
    (swapStep : SpineAtomSwap adjunctionModeSignature pairFirst pairSecond) :
    SaturatedTwoCellConv cellFirst cellSecond :=
  SaturatedTwoCellConv.ofSpineTraceEquiv cellFirst cellSecond
    (by
      rw [firstSpine, secondSpine]
      exact spineTraceEquiv_prependAtoms
        (SpineTraceEquiv.ofStep swapStep.toGodementStep) prefixCells)

/-! ## The COMMUTE `CellDescentResult` builder from the flat swap -/

/-- ★ **The COMMUTE `CellDescentResult` builder from the FLAT located swap.**  Given a `next` cell whose spine is
`cell`'s with the located cup·cap pair transposed to a slot-preserving cap·cup, and the flat located
`SpineAtomSwap (cupAtom :: capAtom :: rest) (capMoved :: cupMoved :: rest)` (produced by
`adjunctionSpineAtomSwap_of_disjointWindows`), package a `CellDescentResult cell`: the `stepConv` is
`commutePrefixSwapCellLift` on the flat swap, the `disorderDrops` is `spineDisorder_swap_lt` inside
`cellDescentResult_ofCommuteStep`.  This is strictly cheaper than the prior `cellDescentResult_ofCommuteStep`,
which required already having the saturated `stepConv` (a boundary-path Godement conversion): here the flat
boundary-length swap suffices.  The oracle's COMMUTE branch is thereby reduced to: exhibit `next` (a cell with
the transposed spine) and the flat located `SpineAtomSwap`. -/
def cellDescentResult_ofCommutePrefixSwap {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath}
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom capMoved cupMoved : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (isCapMoved : capMoved.isCupAtom = false) (isCupMoved : cupMoved.isCupAtom = true)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ capMoved :: cupMoved :: rest)
    (swapStep : SpineAtomSwap adjunctionModeSignature
      (cupAtom :: capAtom :: rest) (capMoved :: cupMoved :: rest)) :
    CellDescentResult cell :=
  cellDescentResult_ofCommuteStep
    (commutePrefixSwapCellLift cell next prefixCells sourceSplit targetSplit swapStep)
    prefixCells rest isCupCup isCapCap isCapMoved isCupMoved sourceSplit targetSplit

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COMMUTE `stepConv` is CHEAP: the flat located swap is the whole conversion.**  Because
the descent is valued in `SaturatedTwoCellConv` and `ofSpineTraceEquiv` lifts any spine trace equivalence
unconditionally, the boundary-LENGTH-level `SpineAtomSwap` the shipped `adjunctionSpineAtomSwap_of_disjointWindows`
produces suffices for the COMMUTE step — no boundary-PATH Godement band-refactor.  `spineTraceEquiv_prependAtoms`
carries the swap behind an arbitrary atom prefix (folding `consCongr`); `commutePrefixSwapCellLift` lifts the
prefixed swap to a cell conversion; `cellDescentResult_ofCommutePrefixSwap` packages the COMMUTE step from the
flat swap plus `next`, discharging `disorderDrops`.

  What this marker does NOT claim — the two COMMUTE INPUTS still owed (gates stay `false`):
  * `next` — a cell with the transposed spine; constructing it needs the cell→chain realization + the
    boundary-path chain surgery (split at prefix, invert the middle pair, re-cons swapped, read back);
  * the flat `SpineAtomSwap` from the `disjointWindows` verdict — the `windowGap` factorization + right/left sign
    from `natWindowDistance ≥ 2`, plus the raw spine's boundary chainedness at the located split.

  And the STRAIGHTEN branch is untouched here: it still owes the adjacent-redex-is-partner bridge (the arc
  non-crossing partner discipline lifted to the cell level, coupled to Piece II) supplying the collapse witness
  `cupFrame ⊟ capFrame ≈ id`.  So `CellDescentStepOracle` stays UN-inhabited; `MatchingReductsShareSpineTrace`,
  `convOfMapEq`, and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyCommuteLift : Bool := true

end FX1Poly.Polygraph
