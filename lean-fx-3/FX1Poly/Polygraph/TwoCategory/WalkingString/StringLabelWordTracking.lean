import FX1Poly.Polygraph.TwoCategory.WalkingString.StringJointInvariant

/-! # WalkingString — the label-boundary-word tracking heart (STRING-JOINT r1, #2219 core)

The FC-1 `capPin` obligation is a projection of the label-boundary-word invariant `labels = pathLabels boundaryWord`
(shipped as `stringCapWindow_notCupWord`).  Its remaining residual is that `advanceLabels` TRACKS `pathLabels` of the
evolving boundary word — the string port of `ArcBoundaryTracking`.  This file BUILDS the substantive heart of that
tracking, zero-axiom:

  * ★ `stringPathLabels_composePath` — `pathLabels` is a monoid homomorphism: `pathLabels (a · b) = pathLabels a ++
    pathLabels b` (cons-only structural, propext-clean — no `List.append_assoc`);
  * ★ the generic splice/de-splice append lemmas `listInsertAt_append_atPrefix` / `listRemoveTwoAt_append_atPrefix`
    over the shipped `listInsertAt` / `listRemoveTwoAt` kit (structural, propext-clean);
  * ★★ `stringAdvanceLabels_tracks_cup` — a CUP's `wireLabelListInsertAt` (splice the cod-word labels at the live
    position) carries `pathLabels (leftContext · rightContext)` to `pathLabels (leftContext · cod · rightContext)`;
  * ★★ `stringAdvanceLabels_tracks_cap` — a CAP's `wireLabelListRemoveTwoAt` carries `pathLabels (leftContext · dom ·
    rightContext)` (dom a length-2 cap word) to `pathLabels (leftContext · rightContext)`.

These two are EXACTLY the per-step preservation of the label-boundary-word invariant `labels = pathLabels boundaryWord`
at a cup / cap.  So the invariant is now a PROVEN fold-preservation, modulo the remaining bookkeeping — a WORD-level
boundary chain `boundaryWord = leftContext · generatorDom · rightContext` per atom (the word analog of the length-only
`SpineBoundaryChained`), threaded so the head atom's decomposition feeds `stringCapWindow_notCupWord`.  That threading
is named in the honesty marker.

Raw Lean 4 + Init; `pathLabels`-hom and the append lemmas are cons-only structural recursion, the tracking is a
region split with the shipped index-shift kit.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## `pathLabels` is a monoid homomorphism -/

/-- ★ **`pathLabels` sends composition to append.**  `pathLabels (composePath first second) = pathLabels first ++
pathLabels second`.  Cons-only structural recursion on `first`: `pathLabels (nil · b) = pathLabels b = [] ++
pathLabels b` (defeq), and `pathLabels (cons m rest · b) = wl m :: pathLabels (rest · b) = wl m :: (pathLabels rest ++
pathLabels b)` by IH.  No `List.append_assoc` / `append_nil` — propext-clean. -/
theorem stringPathLabels_composePath {sourceMode midMode targetMode : AdjointTripleMode} :
    (firstWord : ModalityPath adjointTripleGraph sourceMode midMode) →
    (secondWord : ModalityPath adjointTripleGraph midMode targetMode) →
    pathLabels (composePath firstWord secondWord) = pathLabels firstWord ++ pathLabels secondWord
  | ModalityPath.nil _, secondWord => rfl
  | ModalityPath.cons modality restWord, secondWord => by
      show wireLabelOfModality modality :: pathLabels (composePath restWord secondWord)
        = wireLabelOfModality modality :: (pathLabels restWord ++ pathLabels secondWord)
      rw [stringPathLabels_composePath restWord secondWord]

/-! ## The generic splice / de-splice append lemmas (over the shipped index-shift kit) -/

/-- ★ **Splicing a block at the prefix length splits the append.**  `listInsertAt (prefixList ++ suffixList)
prefixList.length block = prefixList ++ (block ++ suffixList)`.  Structural recursion on `prefixList` using
`listInsertAt`'s cons arm and `listInsertAt_zero`. -/
theorem listInsertAt_append_atPrefix {carrier : Type} :
    (prefixList : List carrier) → (suffixList block : List carrier) →
    listInsertAt (prefixList ++ suffixList) prefixList.length block = prefixList ++ (block ++ suffixList)
  | [], suffixList, block => by
      show listInsertAt suffixList 0 block = block ++ suffixList
      rw [listInsertAt_zero]
  | head :: rest, suffixList, block => by
      show listInsertAt (head :: (rest ++ suffixList)) (rest.length + 1) block
        = head :: (rest ++ (block ++ suffixList))
      show head :: listInsertAt (rest ++ suffixList) rest.length block
        = head :: (rest ++ (block ++ suffixList))
      rw [listInsertAt_append_atPrefix rest suffixList block]

/-- The `listRemoveTwoAt` cons-succ reduction (the def matches list AND position, so this is not a bare `rfl` on an
abstract tail — casing the tail into `[]` / `_ :: _` recovers it, each `rfl`). -/
theorem listRemoveTwoAt_cons_succ {carrier : Type} :
    (head : carrier) → (rest : List carrier) → (position : Nat) →
    listRemoveTwoAt (head :: rest) (position + 1) = head :: listRemoveTwoAt rest position
  | _, [], _ => rfl
  | _, _ :: _, _ => rfl

/-- ★ **Removing the two entries at the prefix length drops the two-block.**  `listRemoveTwoAt (prefixList ++
(firstElem :: secondElem :: suffixList)) prefixList.length = prefixList ++ suffixList`.  Structural recursion on
`prefixList`, peeling the head via `listRemoveTwoAt_cons_succ`. -/
theorem listRemoveTwoAt_append_atPrefix {carrier : Type} :
    (prefixList : List carrier) → (firstElem secondElem : carrier) → (suffixList : List carrier) →
    listRemoveTwoAt (prefixList ++ (firstElem :: secondElem :: suffixList)) prefixList.length
      = prefixList ++ suffixList
  | [], _, _, _ => rfl
  | head :: rest, firstElem, secondElem, suffixList => by
      show listRemoveTwoAt (head :: (rest ++ (firstElem :: secondElem :: suffixList))) (rest.length + 1)
        = head :: (rest ++ suffixList)
      rw [listRemoveTwoAt_cons_succ head (rest ++ (firstElem :: secondElem :: suffixList)) rest.length,
        listRemoveTwoAt_append_atPrefix rest firstElem secondElem suffixList]

/-- ★ **Removing the two entries at the prefix length drops the middle two-block** — the plain-list packaging (the
middle block need only have length 2, no cons-structure exposed).  Casing the middle block on its length-2 shape. -/
theorem listRemoveTwoAt_append_middle {carrier : Type} (prefixList midBlock suffixList : List carrier)
    (midTwo : midBlock.length = 2) :
    listRemoveTwoAt (prefixList ++ (midBlock ++ suffixList)) prefixList.length = prefixList ++ suffixList := by
  cases midBlock with
  | nil => exact Nat.noConfusion midTwo
  | cons firstElem restA =>
      cases restA with
      | nil => exact Nat.noConfusion (Nat.succ.inj midTwo)
      | cons secondElem restB =>
          cases restB with
          | nil =>
              show listRemoveTwoAt (prefixList ++ (firstElem :: secondElem :: suffixList)) prefixList.length
                = prefixList ++ suffixList
              exact listRemoveTwoAt_append_atPrefix prefixList firstElem secondElem suffixList
          | cons _ _ => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj midTwo))

/-! ## ★★ The `advanceLabels`-tracks-`pathLabels` per-step preservation -/

/-- ★★ **A CUP splice tracks `pathLabels`.**  `wireLabelListInsertAt (pathLabels (leftContext · rightContext))
leftContext.length (pathLabels cod) = pathLabels (leftContext · cod · rightContext)`.  The cup's companion label fold
`advanceLabels` (which splices `pathLabels cod` at the live position `leftContext.length`) exactly carries
`pathLabels` of the OLD boundary word (`leftContext · rightContext`, the cup's empty dom collapsed) to `pathLabels` of
the NEW boundary word (`leftContext · cod · rightContext`).  The per-step preservation of the label-boundary-word
invariant at a cup, via `stringPathLabels_composePath` + `listInsertAt_append_atPrefix`. -/
theorem stringAdvanceLabels_tracks_cup {sourceMode midMode targetMode : AdjointTripleMode}
    (leftContext : ModalityPath adjointTripleGraph sourceMode midMode)
    (cod : ModalityPath adjointTripleGraph midMode midMode)
    (rightContext : ModalityPath adjointTripleGraph midMode targetMode) :
    wireLabelListInsertAt (pathLabels (composePath leftContext rightContext)) leftContext.length
        (pathLabels cod)
      = pathLabels (composePath leftContext (composePath cod rightContext)) := by
  show listInsertAt (pathLabels (composePath leftContext rightContext)) leftContext.length (pathLabels cod)
    = pathLabels (composePath leftContext (composePath cod rightContext))
  rw [stringPathLabels_composePath leftContext rightContext,
    stringPathLabels_composePath leftContext (composePath cod rightContext),
    stringPathLabels_composePath cod rightContext,
    show leftContext.length = (pathLabels leftContext).length from (stringPathLabels_length leftContext).symm,
    listInsertAt_append_atPrefix (pathLabels leftContext) (pathLabels rightContext) (pathLabels cod)]

/-- ★★ **A CAP de-splice tracks `pathLabels`.**  For a length-2 cap dom word,
`wireLabelListRemoveTwoAt (pathLabels (leftContext · dom · rightContext)) leftContext.length = pathLabels (leftContext
· rightContext)`.  The cap's companion label fold `advanceLabels` (which removes the two window labels at
`leftContext.length`) exactly carries `pathLabels` of the OLD boundary word to `pathLabels` of the NEW boundary word
(the cap's empty cod collapsed).  The per-step preservation at a cap, via `stringPathLabels_composePath` +
`listRemoveTwoAt_append_atPrefix` (after reading the two-letter cap dom word off the length-2 path). -/
theorem stringAdvanceLabels_tracks_cap {sourceMode midMode targetMode : AdjointTripleMode}
    (leftContext : ModalityPath adjointTripleGraph sourceMode midMode)
    (dom : ModalityPath adjointTripleGraph midMode midMode)
    (rightContext : ModalityPath adjointTripleGraph midMode targetMode) (domTwo : dom.length = 2) :
    wireLabelListRemoveTwoAt (pathLabels (composePath leftContext (composePath dom rightContext)))
        leftContext.length
      = pathLabels (composePath leftContext rightContext) := by
  show listRemoveTwoAt (pathLabels (composePath leftContext (composePath dom rightContext)))
      leftContext.length
    = pathLabels (composePath leftContext rightContext)
  rw [stringPathLabels_composePath leftContext (composePath dom rightContext),
    stringPathLabels_composePath dom rightContext,
    stringPathLabels_composePath leftContext rightContext,
    show leftContext.length = (pathLabels leftContext).length from
      (stringPathLabels_length leftContext).symm]
  -- goal: `listRemoveTwoAt (pathLabels lc ++ (pathLabels dom ++ pathLabels rc)) (pathLabels lc).length
  --        = pathLabels lc ++ pathLabels rc`, and `pathLabels dom` has length 2 (`stringPathLabels_length` + domTwo).
  exact listRemoveTwoAt_append_middle (pathLabels leftContext) (pathLabels dom) (pathLabels rightContext)
    ((stringPathLabels_length dom).trans domTwo)

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the `advanceLabels`-tracks-`pathLabels` per-step preservation is CLOSED (the #2219 heart).**
`pathLabels` is a monoid homomorphism (`stringPathLabels_composePath`, `pathLabels (a · b) = pathLabels a ++ pathLabels
b`), and the generic splice / de-splice append lemmas (`listInsertAt_append_atPrefix` / `listRemoveTwoAt_append_atPrefix`)
give the two per-step tracking facts: a CUP's `wireLabelListInsertAt` carries `pathLabels (lc · rc)` to `pathLabels (lc
· cod · rc)` (`stringAdvanceLabels_tracks_cup`) and a CAP's `wireLabelListRemoveTwoAt` carries `pathLabels (lc · dom ·
rc)` to `pathLabels (lc · rc)` (`stringAdvanceLabels_tracks_cap`).  These ARE the per-step preservation of the
label-boundary-word invariant `labels = pathLabels boundaryWord`, so the invariant is now a PROVEN fold-preservation.
All UNCONDITIONAL, zero-axiom.

The remaining residual to make `capPin` universal-over-reachable (and, with the CAP-orient survivor, flip the headline)
is only the WORD-level boundary chain — a `SpineBoundaryWordChained boundaryWord atoms` giving `boundaryWord =
leftContext · generatorDom · rightContext` at each head atom (the word analog of the shipped length-only
`SpineBoundaryChained`) — threaded so the head decomposition feeds `stringCapWindow_notCupWord`.  That is pure
boundary bookkeeping over `composePath`, mirroring `spineBoundaryChained_spineDiff`; the substantive `pathLabels`
tracking (this file) is DONE.  `= true`. -/
def fxString_hasAdvanceLabelsTracksPathLabels : Bool := true

end FX1Poly.Polygraph
