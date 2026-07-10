import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelWordTracking
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryWordChain

/-! # WalkingString — the reachable-`capPin` fold over the boundary-WORD chain (STRING-JOINT r2, WALL 2 brick B)

WALL 2 brick A shipped the boundary-WORD-chain substrate `SpineBoundaryWordChained` (`SpineBoundaryWordChain.lean`),
delivering `boundaryWord = leftContext · generatorDom · rightContext` at each head atom, and the #2219 heart shipped
the `advanceLabels`-tracks-`pathLabels` per-step facts (`StringLabelWordTracking.lean`).  This file THREADS them:
it eliminates the FALSE universal-over-disciplined `capPin` hypothesis of the FC-1 conditional
(`stringMatchingOf_loops_zero_ofDisciplinePreserved`, whose `capPin` is unprovable — a free-label disciplined state
reads a cup word at a cap window) and REPLACES it by a PROVEN reachable-`capPin` fold, derived UNCONDITIONALLY from
the word chain.

## What closes here (each zero-axiom, WALL-2-only — no orientation discipline, no `preserves`)

  * `advanceLabels_ofCupArity` / `advanceLabels_ofCapArity` — the arity reductions of the label companion fold (the
    label analog of the shipped `stepAtom_ofCupArity` / `_ofCapArity`);
  * `pathLabels_lengthZero_nil` — a length-0 1-cell has empty label word (the empty-middle collapse);
  * ★ `stringAdvanceLabels_tracksWordChain` — at a cup/cap atom firing at `boundaryWord = lc · dom · rc`, the label
    companion carries `pathLabels boundaryWord` to `pathLabels (lc · cod · rc)` (the tail's boundary word), via the
    shipped append lemmas — so the label-boundary-word invariant `labels = pathLabels boundaryWord` is a fold
    invariant;
  * ★★ `StringCapPinAlongFold` + `stringCapPinAlongFold_ofWordChain` — the reachable-`capPin` fold: threading the word
    chain, the arity discipline, and the length invariant `state.openWires.length = boundaryWord.length`, at EVERY cap
    the window is in range and reads a NON-cup (cap) word.  The window-in-range half is the boundary decomposition's
    length, the not-cup-word half is the shipped `stringCapWindow_notCupWord` fed by the chain's head decomposition;
  * ★★ `stringCapPinAlongFold_fromCell` — the cell-level capstone: every cup/cap cell's spine, from the fresh seed,
    satisfies the reachable-`capPin` fold.  Non-vacuous on a bare cap (`stringCounitLower`) and on the cross-level cell.

## The residual to full `CapsDistinctAlongFold` (the assembly)

`CapsDistinctAlongFold` additionally needs the cap window to be DISTINCT-component, which the chirality refutation
`stringDisciplinedCap_windowDistinct` (shipped) derives from the ORIENTATION discipline + this not-cup-word fact.
Threading the discipline is the cap-orient survivor `stringOrientationDiscipline_stepCap` (WALL 1) plus the shipped
cup-orient — the assembly.  This file DISCHARGES the `capPin` residual; the `preserves`/orient residual is WALL 1.

Raw Lean 4 + Init; the arity reductions mirror `stepAtom_ofCupArity`, the tracking is the shipped append lemmas, the
fold is structural list recursion reusing `stepAtom_openWires_tracksBoundary` for the length invariant.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The label companion arity reductions -/

/-- ★ **The label companion fold at CUP arity.**  A `0 ⇒ 2` atom's `advanceLabels` splices the cod-word labels at
the live position — the label analog of `stepAtom_ofCupArity`. -/
theorem advanceLabels_ofCupArity {sourceMode targetMode : AdjointTripleMode}
    (labels : List WireLabel) (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (hdom : atom.generatorDom.length = 0) (hcod : atom.generatorCod.length = 2) :
    advanceLabels labels atom
      = wireLabelListInsertAt labels atom.leftContext.length (pathLabels atom.generatorCod) := by
  unfold advanceLabels
  rw [hdom, hcod]

/-- ★ **The label companion fold at CAP arity.**  A `2 ⇒ 0` atom's `advanceLabels` removes the two window labels at
the live position — the label analog of `stepAtom_ofCapArity`. -/
theorem advanceLabels_ofCapArity {sourceMode targetMode : AdjointTripleMode}
    (labels : List WireLabel) (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (hdom : atom.generatorDom.length = 2) (hcod : atom.generatorCod.length = 0) :
    advanceLabels labels atom = wireLabelListRemoveTwoAt labels atom.leftContext.length := by
  unfold advanceLabels
  rw [hdom, hcod]

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem capPinRangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := capPinRangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem capPinRangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [capPinRangeLoopLength count []]; exact Nat.add_zero count

/-- The fresh seed's open-wire count is the boundary width. -/
theorem stringInitialWireState_openWires_length (bottomCount : Nat) :
    (stringInitialWireState bottomCount).openWires.length = bottomCount :=
  capPinRangeLength bottomCount

/-! ## The empty-middle collapse -/

/-- A length-0 list is empty (propext-clean: the cons case is `Nat.noConfusion` on `succ = 0`). -/
private theorem listLengthZeroNil {carrier : Type} :
    (list : List carrier) → list.length = 0 → list = []
  | [], _ => rfl
  | _ :: _, lenEq => Nat.noConfusion lenEq

/-- ★ **A length-0 1-cell has empty label word.**  `pathLabels` preserves length (`stringPathLabels_length`), so a
length-0 path's label word has length 0, hence is `[]`. -/
theorem pathLabels_lengthZero_nil {sourceMode targetMode : AdjointTripleMode}
    (path : ModalityPath adjointTripleGraph sourceMode targetMode) (lenZero : path.length = 0) :
    pathLabels path = [] :=
  listLengthZeroNil (pathLabels path) ((stringPathLabels_length path).trans lenZero)

/-! ## ★ The label-boundary-word invariant is a fold invariant -/

/-- ★★ **The label companion tracks the boundary word through one cup/cap atom.**  If the head atom fires at
`boundaryWord = leftContext · generatorDom · rightContext`, then `advanceLabels (pathLabels boundaryWord) atom` equals
`pathLabels (leftContext · generatorCod · rightContext)` — the tail's boundary word.  A cup splices the cod labels
(empty dom collapses); a cap removes the two dom labels (empty cod collapses).  So the invariant
`labels = pathLabels boundaryWord` is preserved by every atom.  Proved directly over the shipped `pathLabels`-hom and
splice/de-splice append lemmas (no dependent mode-collapse needed). -/
theorem stringAdvanceLabels_tracksWordChain {sourceMode targetMode : AdjointTripleMode}
    (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (boundaryWord : ModalityPath adjointTripleGraph sourceMode targetMode)
    (arity : AtomHasCupOrCapArity atom)
    (headFires : boundaryWord
      = composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)) :
    advanceLabels (pathLabels boundaryWord) atom
      = pathLabels (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)) := by
  subst headFires
  have leftLenEq : atom.leftContext.length = (pathLabels atom.leftContext).length :=
    (stringPathLabels_length atom.leftContext).symm
  have expandDom : pathLabels
        (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext))
      = pathLabels atom.leftContext ++ (pathLabels atom.generatorDom ++ pathLabels atom.rightContext) := by
    rw [stringPathLabels_composePath atom.leftContext (composePath atom.generatorDom atom.rightContext),
      stringPathLabels_composePath atom.generatorDom atom.rightContext]
  have expandCod : pathLabels
        (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
      = pathLabels atom.leftContext ++ (pathLabels atom.generatorCod ++ pathLabels atom.rightContext) := by
    rw [stringPathLabels_composePath atom.leftContext (composePath atom.generatorCod atom.rightContext),
      stringPathLabels_composePath atom.generatorCod atom.rightContext]
  cases arity with
  | inl cupArity =>
      obtain ⟨domZero, codTwo⟩ := cupArity
      have domNil : pathLabels atom.generatorDom = [] := pathLabels_lengthZero_nil atom.generatorDom domZero
      refine (advanceLabels_ofCupArity (pathLabels
        (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)))
        atom domZero codTwo).trans ?_
      show listInsertAt (pathLabels
          (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)))
          atom.leftContext.length (pathLabels atom.generatorCod)
        = pathLabels (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
      rw [expandDom, domNil, List.nil_append, expandCod, leftLenEq,
        listInsertAt_append_atPrefix (pathLabels atom.leftContext) (pathLabels atom.rightContext)
          (pathLabels atom.generatorCod)]
  | inr capArity =>
      obtain ⟨domTwo, codZero⟩ := capArity
      have codNil : pathLabels atom.generatorCod = [] := pathLabels_lengthZero_nil atom.generatorCod codZero
      refine (advanceLabels_ofCapArity (pathLabels
        (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)))
        atom domTwo codZero).trans ?_
      show listRemoveTwoAt (pathLabels
          (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)))
          atom.leftContext.length
        = pathLabels (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
      rw [expandDom, expandCod, codNil, List.nil_append, leftLenEq,
        listRemoveTwoAt_append_middle (pathLabels atom.leftContext) (pathLabels atom.generatorDom)
          (pathLabels atom.rightContext) ((stringPathLabels_length atom.generatorDom).trans domTwo)]

/-! ## ★★ The reachable-`capPin` fold -/

/-- ★★ **The reachable-`capPin` fold obligation.**  Threaded through the spine, every atom that is a CAP
(`generatorDom.length = 2`, `generatorCod.length = 0`) fires on a window that is IN RANGE and reads a NON-cup (cap)
word.  This is EXACTLY the FC-1 `capPin` conclusion, but as a FOLD over the reachable states — no longer a hypothesis. -/
def StringCapPinAlongFold {sourceMode targetMode : AdjointTripleMode} :
    WireState → List WireLabel → List (SpineAtom adjointTripleModeSignature sourceMode targetMode) → Prop
  | _, _, [] => True
  | state, labels, atom :: rest =>
      (atom.generatorDom.length = 2 → atom.generatorCod.length = 0 →
        atom.leftContext.length + 1 < state.openWires.length
          ∧ isCupWordOrdered (wireLabelListGetAt labels atom.leftContext.length)
              (wireLabelListGetAt labels (atom.leftContext.length + 1)) = false)
      ∧ StringCapPinAlongFold (stepAtom state atom) (advanceLabels labels atom) rest

/-- ★★ **The reachable-`capPin` fold is DISCHARGED from the boundary-word chain.**  Given the arity discipline
(`SpineHasCupCapAtoms`), the boundary-word chain (`SpineBoundaryWordChained boundaryWord atoms`), and the length
invariant `state.openWires.length = boundaryWord.length`, the reachable-`capPin` fold holds outright (with labels
`pathLabels boundaryWord`): at each head atom the chain's decomposition `boundaryWord = lc · dom · rc` gives the
window range (its length) and the cap-word read (`stringCapWindow_notCupWord`), the length invariant is re-established
via `stepAtom_openWires_tracksBoundary`, and the label invariant via `stringAdvanceLabels_tracksWordChain`.  Structural
list recursion; UNCONDITIONAL (no orientation discipline).  This makes the FC-1 `capPin` universal-over-REACHABLE — a
consequence of the word chain, not an assumption. -/
theorem stringCapPinAlongFold_ofWordChain {sourceMode targetMode : AdjointTripleMode} :
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) →
    (state : WireState) →
    (boundaryWord : ModalityPath adjointTripleGraph sourceMode targetMode) →
    SpineHasCupCapAtoms atoms →
    SpineBoundaryWordChained boundaryWord atoms →
    state.openWires.length = boundaryWord.length →
    StringCapPinAlongFold state (pathLabels boundaryWord) atoms
  | [], _, _, _, _, _ => trivial
  | atom :: rest, state, boundaryWord, arityAll, wordChained, tracksLength => by
      obtain ⟨headArity, tailArity⟩ := spineHasCupCapAtoms_tail arityAll
      obtain ⟨headFires, tailChained⟩ := spineBoundaryWordChained_tail wordChained
      have wordLenEqDom : boundaryWord.length = atom.domBoundaryLength := by
        rw [headFires]
        show (composePath atom.leftContext (composePath atom.generatorDom atom.rightContext)).length
          = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
        rw [ModalityPath.length_composePath atom.leftContext
            (composePath atom.generatorDom atom.rightContext),
          ModalityPath.length_composePath atom.generatorDom atom.rightContext, Nat.add_assoc]
      have tracksEntry : state.openWires.length = atom.domBoundaryLength := tracksLength.trans wordLenEqDom
      refine ⟨?_, ?_⟩
      · intro domTwo codZero
        refine ⟨?_, ?_⟩
        · rw [tracksEntry]
          show atom.leftContext.length + 1
            < atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
          rw [domTwo]
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1))
            (Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length)
        · exact stringCapWindow_notCupWord atom (pathLabels boundaryWord)
            (congrArg pathLabels headFires) domTwo codZero
      · have newTracks : (stepAtom state atom).openWires.length
            = (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)).length := by
          rw [stepAtom_openWires_tracksBoundary state atom headArity tracksEntry]
          show atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length
            = (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext)).length
          rw [ModalityPath.length_composePath atom.leftContext
              (composePath atom.generatorCod atom.rightContext),
            ModalityPath.length_composePath atom.generatorCod atom.rightContext, Nat.add_assoc]
        rw [stringAdvanceLabels_tracksWordChain atom boundaryWord headArity headFires]
        exact stringCapPinAlongFold_ofWordChain rest (stepAtom state atom)
          (composePath atom.leftContext (composePath atom.generatorCod atom.rightContext))
          tailArity tailChained newTracks

/-- ★★ **The cell-level reachable-`capPin` capstone.**  For every cup/cap-generated string cell, the reachable-`capPin`
fold holds over its spine from the fresh seed (labels `pathLabels sourcePath`): the boundary-word chain seed
(`spineBoundaryWordChained_spine`), the arity discipline (`spineHasCupCapAtoms_spine`), and the length seed (the range
list's length) feed `stringCapPinAlongFold_ofWordChain`. -/
theorem stringCapPinAlongFold_fromCell {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (cellCupCap : CellHasCupCapGenerators cell) :
    StringCapPinAlongFold (stringInitialWireState sourcePath.length) (pathLabels sourcePath) cell.spine :=
  stringCapPinAlongFold_ofWordChain cell.spine (stringInitialWireState sourcePath.length) sourcePath
    (RawTwoCellExpr.spineHasCupCapAtoms_spine cell cellCupCap)
    (RawTwoCellExpr.spineBoundaryWordChained_spine cell)
    (stringInitialWireState_openWires_length sourcePath.length)

/-! ## Non-vacuity — the fold bites on real cap-carrying cells -/

/-- ★ **Non-vacuity: a bare CAP cell.**  `stringCounitLower : G·F ⇒ id_tip` is a single-cap cell (its spine has one
cap atom, whose window reads the cap word `[G, F]`); the reachable-`capPin` fold holds over it. -/
theorem stringCapPinAlongFold_stringCounitLower :
    StringCapPinAlongFold (stringInitialWireState stringGF.length) (pathLabels stringGF) stringCounitLower.spine :=
  stringCapPinAlongFold_fromCell stringCounitLower (Or.inr ⟨rfl, rfl⟩)

/-- ★ **Non-vacuity: the CROSS-LEVEL cell.**  `stringCrossLevelCell : G·F ⇒ G·H` (a real cap `ε` then a real cup `η'`,
in neither single adjunction) — the reachable-`capPin` fold holds over its two-atom spine. -/
theorem stringCapPinAlongFold_stringCrossLevelCell :
    StringCapPinAlongFold (stringInitialWireState stringGF.length) (pathLabels stringGF)
      stringCrossLevelCell.spine :=
  stringCapPinAlongFold_fromCell stringCrossLevelCell ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the FC-1 `capPin` is now universal-over-REACHABLE, DISCHARGED from the boundary-word chain.**
The label companion arity reductions (`advanceLabels_ofCupArity` / `_ofCapArity`), the empty-middle collapse
(`pathLabels_lengthZero_nil`), and the fold-invariance of the label-boundary-word equation
(`stringAdvanceLabels_tracksWordChain`: `advanceLabels (pathLabels (lc·dom·rc)) atom = pathLabels (lc·cod·rc)`) thread
the shipped word chain + #2219 tracking heart into the reachable-`capPin` fold `StringCapPinAlongFold`, DISCHARGED
UNCONDITIONALLY for every cup/cap cell by `stringCapPinAlongFold_ofWordChain` / `_fromCell` (the length invariant via
`stepAtom_openWires_tracksBoundary`, the not-cup-word read via the shipped `stringCapWindow_notCupWord`).  So the FC-1
conditional's FALSE `capPin` hypothesis (universal-over-disciplined) is REPLACED by a PROVEN fact
(universal-over-reachable).  Non-vacuous on a bare cap (`stringCounitLower`) and the cross-level cell.  The remaining
residual to full `CapsDistinctAlongFold` is only the ORIENTATION discipline's distinctness (WALL 1's cap-orient +
shipped cup-orient), the assembly.  All UNCONDITIONAL, zero-axiom.  `= true`. -/
def fxString_hasReachableCapPinFold : Bool := true

end FX1Poly.Polygraph
