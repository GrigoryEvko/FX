import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeInversion
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallBlockScaffold

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallFreePathInjectivity — the PATH-level injectivity of the right
coprojection's 1-cell functor, via WORD reflection (WP-AMALG-2 r10, B1 — node (i)'s shared-middle reconciliation)

`PushoutWallFreeInversion.lean` (B1) shipped the LETTER-level converse `retractRightLetter` and
`embedRightLetter_injective`.  The r10 recon's node (i) vcomp case needs the PATH-level lift: the induced 1-cell
functor `mapPath (inclusionRight …)` on monad 1-cells is INJECTIVE — the "shared-middle reconciliation" that lets
the two middle pre-images of a `vcomp` coincide.

## Why the direct `injection` route jams — and the word reflection that dodges it

`mapPath (inclusionRight …) (cons letter rest) = cons (mapModality letter) (mapPath rest)` has TYPE INDICES that are
function applications `(inclusionRight …).onModes middleMode`, NOT constructors — so `injection` on a MAPPED cons
equality drills those index equalities indefinitely (the "childCons injection drilling" landmine) and never reaches
the payload.  The fix is to reflect the dependent `ModalityPath` cons through the NON-dependent boundary WORD:

  * `monadPathWord` reads a monad 1-cell to its `List` of generator indices;
  * `mapPath_inclRight_word` proves `pushoutPathWord ∘ mapPath (inclusionRight …) = List.map (embedRightLetter …)
    ∘ monadPathWord` (a build-only induction — `congrArg`, no destructuring);
  * `mapEmbedRight_injective` cancels the injective `embedRightLetter` under `List.map` (non-dependent `List`
    `injection`);
  * `monadPathWord_injective` recovers the path from its word — the ONE dependent `cons` reconstruction, whose
    shared middle mode is pinned by the generator's recorded endpoints (`letter.property`, a `Prod.snd` `congrArg`),
    then `subst` + `Subtype.ext` closes it (RAW monad conses have variable indices, so `subst` is clean here).

`mapPath_inclRight_injective` then composes these: equal mapped paths ⟹ equal boundary words ⟹ (cancel
`embedRightLetter`) equal monad words ⟹ (recover) equal monad paths.  No `castBoundary`, no `omega`, no propext.

## What STAYS WALLED (no flip)

This is 1-cell injectivity — NOT `pathInvert` (the wall-free 1-cell CONVERSE producing a monad pre-image), NOT the
CELL-level `wallFreeCellInvert`.  Those are the named downstream nodes.
`fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`; `fxAmalg_hasGeneralPushoutDispatch` STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The right coprojection's 1-generator functor is injective -/

/-- ★ **`mapModality (inclusionRight …)` is injective.**  A monad modality maps to the Subtype whose `.val` is
`embedRightLetter … mod.val`; equal images give equal `embedRightLetter`-values, so `embedRightLetter_injective`
recovers equal `.val`s and `Subtype.ext` (proof-irrelevant) closes.  Propext-free. -/
theorem mapModality_inclRight_injective {sourceMode targetMode : Fin monadComputad.modeCount}
    {modA modB : monadComputad.Modality sourceMode targetMode}
    (equalImages :
      mapModality (inclusionRight involutionComputad monadComputad involutionMonadSameModes) modA
        = mapModality (inclusionRight involutionComputad monadComputad involutionMonadSameModes) modB) :
    modA = modB :=
  Subtype.ext
    (embedRightLetter_injective involutionComputad monadComputad involutionMonadSameModes
      (congrArg Subtype.val equalImages))

/-! ## The monad boundary word and the coprojection's word law -/

/-- The **boundary word of a monad 1-cell** — each `cons` letter's generator index, read off the path (the monad
analogue of `pushoutPathWord`).  Structural on the path. -/
def monadPathWord : {sourceMode targetMode : Fin monadComputad.modeCount} →
    ModalityPath monadComputad.toModeGraph sourceMode targetMode →
    List (Fin monadComputad.modalityGenerators.length)
  | _, _, .nil _ => []
  | _, _, .cons letter rest => letter.val :: monadPathWord rest

/-- ★ **The coprojection's WORD law** — `pushoutPathWord ∘ mapPath (inclusionRight …)` equals `List.map
(embedRightLetter …) ∘ monadPathWord`: mapping a monad 1-cell into the pushout then reading its word is the same as
reading its monad word and retagging each letter.  A build-only induction (`congrArg`): the `cons` head aligns
because `(mapModality (inclusionRight …) letter).val = embedRightLetter … letter.val` definitionally. -/
theorem mapPath_inclRight_word :
    {sourceMode targetMode : Fin monadComputad.modeCount} →
    (path : ModalityPath monadComputad.toModeGraph sourceMode targetMode) →
    pushoutPathWord (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) path)
      = (monadPathWord path).map (embedRightLetter involutionComputad monadComputad involutionMonadSameModes)
  | _, _, .nil _ => rfl
  | _, _, .cons letter rest =>
      congrArg (embedRightLetter involutionComputad monadComputad involutionMonadSameModes letter.val :: ·)
        (mapPath_inclRight_word rest)

/-! ## Cancelling the injective retag under `List.map` -/

/-- ★ **`List.map (embedRightLetter …)` is injective** — the retag is injective (`embedRightLetter_injective`), so
mapping it over two lists is injective.  Structural on the lists; the `nil`/`cons` mismatches contradict via
`List.noConfusion`, the `cons`/`cons` case `injection`s the (non-dependent) `List` cons and cancels the retag on the
head, recursing on the tail.  Propext-free. -/
theorem mapEmbedRight_injective :
    (listA listB : List (Fin monadComputad.modalityGenerators.length)) →
    listA.map (embedRightLetter involutionComputad monadComputad involutionMonadSameModes)
        = listB.map (embedRightLetter involutionComputad monadComputad involutionMonadSameModes) →
    listA = listB
  | [], [], _ => rfl
  | [], _ :: _, equalImages => Nat.noConfusion (congrArg List.length equalImages)
  | _ :: _, [], equalImages => Nat.noConfusion (congrArg List.length equalImages)
  | headA :: tailA, headB :: tailB, equalImages => by
      injection equalImages with headEqual tailEqual
      have headMonadEqual : headA = headB :=
        embedRightLetter_injective involutionComputad monadComputad involutionMonadSameModes headEqual
      subst headMonadEqual
      exact congrArg (headA :: ·) (mapEmbedRight_injective tailA tailB tailEqual)

/-! ## Recovering the monad 1-cell from its word -/

/-- ★★ **`monadPathWord` is injective** — a monad 1-cell is determined by its boundary word.  Structural on the two
paths: `nil`/`cons` mismatches contradict via `List.noConfusion`; the `cons`/`cons` case `injection`s the
(non-dependent) `List` word equality into head-index and tail-word equalities, pins the shared middle mode from the
head letter's recorded endpoints (`letter.property`, a `Prod.snd` `congrArg`), `subst`s it (RAW monad cons indices
are variables — clean), identifies the two head letters by `Subtype.ext`, and recurses on the tail.  Propext-free. -/
theorem monadPathWord_injective :
    {sourceMode targetMode : Fin monadComputad.modeCount} →
    (pathA pathB : ModalityPath monadComputad.toModeGraph sourceMode targetMode) →
    monadPathWord pathA = monadPathWord pathB → pathA = pathB
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .nil _, .cons _ _, equalWords => Nat.noConfusion (congrArg List.length equalWords)
  | _, _, .cons _ _, .nil _, equalWords => Nat.noConfusion (congrArg List.length equalWords)
  | _, _, @ModalityPath.cons _ _ middleA _ letterA restA,
          @ModalityPath.cons _ _ middleB _ letterB restB, equalWords => by
      injection equalWords with headValEqual tailWordEqual
      have middleEqual : middleA = middleB := by
        have getEqual : monadComputad.modalityGenerators.get letterA.val
            = monadComputad.modalityGenerators.get letterB.val :=
          congrArg (monadComputad.modalityGenerators.get ·) headValEqual
        exact congrArg Prod.snd (letterA.property.symm.trans (getEqual.trans letterB.property))
      subst middleEqual
      have letterEqual : letterA = letterB := Subtype.ext headValEqual
      subst letterEqual
      have restEqual : restA = restB := monadPathWord_injective restA restB tailWordEqual
      subst restEqual
      rfl

/-! ## The path-level injectivity -/

/-- ★★★ **`mapPath (inclusionRight …)` is injective on monad 1-cells.**  Equal mapped paths have equal boundary
words (`congrArg pushoutPathWord`), which are `embedRightLetter`-retags of the monad words (`mapPath_inclRight_word`);
cancelling the retag (`mapEmbedRight_injective`) gives equal monad words, and recovering the path from its word
(`monadPathWord_injective`) gives equal monad paths.  This is the shared-middle reconciliation node (i)'s vcomp case
needs — the right coprojection's 1-cell functor is faithful.  Propext-free. -/
theorem mapPath_inclRight_injective {sourceMode targetMode : Fin monadComputad.modeCount}
    (pathA pathB : ModalityPath monadComputad.toModeGraph sourceMode targetMode)
    (equalImages :
      mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) pathA
        = mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) pathB) :
    pathA = pathB :=
  monadPathWord_injective pathA pathB
    (mapEmbedRight_injective (monadPathWord pathA) (monadPathWord pathB)
      ((mapPath_inclRight_word pathA).symm.trans
        ((congrArg pushoutPathWord equalImages).trans (mapPath_inclRight_word pathB))))

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the PATH-level right-coprojection 1-cell injectivity SHIPS (WP-AMALG-2 r10, B1).**
`= true`: `mapModality_inclRight_injective` (via `embedRightLetter_injective` + `Subtype.ext`) and
`mapPath_inclRight_injective` (via the WORD reflection `monadPathWord` / `mapPath_inclRight_word` /
`mapEmbedRight_injective` / `monadPathWord_injective`, dodging the childCons injection-drilling landmine on the
function-application-indexed mapped cons).  This is the shared-middle reconciliation node (i)'s vcomp case needs:
the two middle pre-images of a `vcomp` coincide because the right coprojection's 1-cell functor is faithful.  It is
NOT `pathInvert` (the wall-free 1-cell converse) nor `wallFreeCellInvert` (the cell-level essential-surjectivity
converse); those are the named downstream nodes.  No marker flips.  `= true`. -/
def fxAmalg_hasWallFreePathInjectivity : Bool := true

end FX1Poly.Polygraph.Amalgam
