import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojection
import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/DispatchMap — the block factorization + the dispatch map, assembled on a REAL
combined cell (WP-AMALG-2 r1, B1)

The two ingredients the categorical Nelson-Oppen dispatch needs — the 1-cell BLOCK FACTORIZATION
(`InterleavingNF.blockDecompose`, the Nyberg-Brodda alternating normal form) and the coprojection CELL FUNCTOR
(`MapCell.mapCellAlong`, the transport of a component 2-cell into the pushout) — both already ship.  This file
ASSEMBLES them into the dispatch's routing content and exercises it NON-VACUOUSLY on a genuinely combined cell.

## What ships here (each piece zero-axiom, structural, ASCII-only, computes under `#eval`)

  * **`blockTags`** — the **dispatch routing map**: read a pushout boundary word, block-decompose it, and return
    the per-block component TAGS (the sequence of component deciders each maximal block routes to).  This is the
    literal dispatch schedule: `[true, false, ...]` = "block 1 to component 1, block 2 to component 2, ...".
  * **`wordAllComponentTwo`** + **`monoFalseBlocks`** + **`monoBlockDecompose`** — the **block-purity of a
    dispatch-map image**: a coprojected (single-component) word block-decomposes to at most ONE block (a component
    image occupies a single block, so it dispatches to a single component decider).  The general reason the right
    coprojection's images are block-pure.
  * **`dispatchedMonadUnit`** + **`dispatchedMonadUnit_isGen`** — the dispatch map FIRING on a REAL component
    generator: `mapCellAlong inclusionRightTwoReal (gen eta)` lands the genuine pushout generating 2-cell (index 0,
    `RealCoprojection.inclusionRightTwoReal_onUnit_index`) — not a vacuous `Fin.elim0`.
  * **The non-vacuity contrast** — `crossPairDomainRouting` (a REAL combined cell's boundary `s·t` routes to TWO
    blocks `[true, false]`), `monadTailWord_singleBlock` (a dispatch-map image's boundary `t·t` routes to ONE
    block).  The dispatch genuinely SPLITS a mixed cell and leaves a coprojected cell whole.

## Where this sits in the dispatch

The block factorization is the DOMAIN decomposition (which component handles each stretch of the boundary); the
dispatch map is the coprojection that EMBEDS a component decision back into the pushout.  Together they are the
1-cell substrate the saturated dispatch (`DispatchSaturated` / `ComposableFragmentDispatch`) runs the 2-cell
convertibility over.  Non-vacuity is carried entirely by concrete `rfl` computations on the `involution +_M monad`
witness pushout.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The dispatch routing map -/

/-- ★ **The dispatch routing map** — the per-block component TAGS of a pushout boundary word.  Block-decompose the
word into maximal same-component blocks (`blockDecompose`), then read off each block's tag: the resulting `List
Bool` is the schedule that says which component decider each maximal block routes to (`true` = component 1,
`false` = component 2).  Computes. -/
def blockTags (splitPoint : Nat) {bound : Nat} (word : List (Fin bound)) : List Bool :=
  (blockDecompose splitPoint word).map (fun block => block.1)

/-- The routing map recovers nothing new — recomposing the decomposition it reads recovers the word (a restatement
of `blockDecompose_sound`, so the routing does not lose the boundary). -/
theorem blockTags_recompose_sound (splitPoint : Nat) {bound : Nat} (word : List (Fin bound)) :
    recompose (blockDecompose splitPoint word) = word :=
  blockDecompose_sound splitPoint word

/-! ## Block-purity of a dispatch-map image (a coprojected word is a single block) -/

/-- Whether every letter of a word lies in component 2 (its tag is `false` — `letterTag` at or above the split).
Recursive `Bool` via `!letterTag`, propext-free. -/
def wordAllComponentTwo (splitPoint : Nat) {bound : Nat} : List (Fin bound) → Bool
  | [] => true
  | letter :: rest => (! letterTag splitPoint letter) && wordAllComponentTwo splitPoint rest

/-- The single-block image of a component-2 (mono-component) word — empty stays empty, non-empty becomes one
`false`-tagged block. -/
def monoFalseBlocks {bound : Nat} : List (Fin bound) → List (TaggedBlock bound)
  | [] => []
  | letter :: rest => [(false, letter :: rest)]

/-- ★ **Block-purity** — a mono-component-2 word block-decomposes to `monoFalseBlocks` (at most one block).  This is
why a dispatch-map image (a coprojected component cell, whose boundary is entirely one component's letters) occupies
a SINGLE block and dispatches to a single component decider; a genuinely mixed cell spans several.  Structural on
the word: the head tag is `false` (from `wordAllComponentTwo`), so `prependLetter` always MERGES into the running
false block. -/
theorem monoBlockDecompose (splitPoint : Nat) {bound : Nat} (word : List (Fin bound))
    (allTwo : wordAllComponentTwo splitPoint word = true) :
    blockDecompose splitPoint word = monoFalseBlocks word := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      have splitHyp : ((! letterTag splitPoint letter) && wordAllComponentTwo splitPoint rest) = true := allTwo
      have htagFalse : letterTag splitPoint letter = false := by
        cases htag : letterTag splitPoint letter with
        | false => rfl
        | true =>
            rw [htag, Bool.not_true, Bool.false_and] at splitHyp
            exact Bool.noConfusion splitHyp
      have hrest : wordAllComponentTwo splitPoint rest = true := by
        rw [htagFalse, Bool.not_false, Bool.true_and] at splitHyp
        exact splitHyp
      have ihEq : blockDecompose splitPoint rest = monoFalseBlocks rest := ih hrest
      show prependLetter splitPoint letter (blockDecompose splitPoint rest) = monoFalseBlocks (letter :: rest)
      rw [ihEq]
      cases rest with
      | nil =>
          show prependLetter splitPoint letter [] = [(false, [letter])]
          unfold prependLetter
          rw [htagFalse]
      | cons headLetter moreLetters =>
          show prependLetter splitPoint letter [(false, headLetter :: moreLetters)]
            = [(false, letter :: headLetter :: moreLetters)]
          unfold prependLetter
          rw [htagFalse]

/-- A mono-component-2 word occupies at most one block (`monoFalseBlocks` has length 0 or 1) — the block-count
corollary of block-purity. -/
theorem monoBlockDecompose_lengthLeOne (splitPoint : Nat) {bound : Nat} (word : List (Fin bound))
    (allTwo : wordAllComponentTwo splitPoint word = true) :
    (blockDecompose splitPoint word).length ≤ 1 := by
  rw [monoBlockDecompose splitPoint word allTwo]
  cases word with
  | nil => exact Nat.le_of_lt (Nat.lt_succ_of_le (Nat.le_refl 0))
  | cons _ _ => exact Nat.le_refl 1

/-! ## The dispatch map FIRING on a real component generator -/

/-- ★ **The dispatch map on the REAL monad unit** — `mapCellAlong` along the genuine right coprojection
`inclusionRightTwoReal`, applied to the monad component's `eta` generating 2-cell.  A real component cell TRANSPORTED
into the pushout by the dispatch map (not a vacuous `Fin.elim0`). -/
def dispatchedMonadUnit :=
  mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (RawTwoCellExpr.gen monadComputadReconstructsUnit)

/-- The dispatch map of a generating 2-cell is the generator at its `onTwoCell` image (`mapCellAlong` maps `gen` on
the nose) — so `dispatchedMonadUnit` IS the pushout generating 2-cell the coprojection assigns. -/
theorem dispatchedMonadUnit_isGen :
    dispatchedMonadUnit = RawTwoCellExpr.gen
      ((inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes).onTwoCell
        monadComputadReconstructsUnit) := rfl

/-- ★ **Non-vacuity of the dispatch map** — the dispatched monad unit lands at pushout 2-generator index `0` (the
retagged `eta`; `involutionComputad` contributes no 2-generators so the shift is `0`).  Restates
`RealCoprojection.inclusionRightTwoReal_onUnit_index` at the dispatch-map image, confirming the map fires on a
genuine generator. -/
theorem dispatchedMonadUnit_index :
    ((inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes).onTwoCell
        monadComputadReconstructsUnit).val.val = 0 :=
  inclusionRightTwoReal_onUnit_index

/-! ## Non-vacuity: the routing of a REAL combined cell vs a dispatch-map image (each `rfl`) -/

/-- ★ **A real combined cell's boundary routes to TWO blocks** — the domain word `s·t` of the genuinely combined
`crossPairAlpha` (`DeciderReseat`) dispatches to `[true, false]` (a component-1 block then a component-2 block).
Non-vacuous: the dispatch genuinely SPLITS the mixed boundary.  `rfl`. -/
theorem crossPairDomainRouting :
    blockTags involutionMonadSplit crossPairDomainWord = [true, false] := rfl

/-- The four-block routing of the alternating witness word `s t s t t` — `[true, false, true, false]`.  `rfl`. -/
theorem witnessWordRouting :
    blockTags involutionMonadSplit witnessWord = [true, false, true, false] := rfl

/-- The real combined cell's boundary decomposes into exactly TWO blocks (genuinely mixed). -/
theorem crossPairDomain_multiBlock :
    (blockDecompose involutionMonadSplit crossPairDomainWord).length = 2 := rfl

/-- The pure monad-tail word `t·t` — a dispatch-map image's boundary (component 2 only). -/
def monadTailWord : List (Fin involutionMonadPushout.modalityGenerators.length) := [tLetter, tLetter]

/-- The monad tail is all component 2 (`wordAllComponentTwo = true`, `rfl`). -/
theorem monadTailWord_allTwo :
    wordAllComponentTwo involutionMonadSplit monadTailWord = true := rfl

/-- ★ **A dispatch-map image's boundary routes to ONE block** — the pure monad tail `t·t` dispatches to the single
component-2 block `[(false, t t)]`, confirming block-purity concretely (contrast `crossPairDomainRouting`, which
splits into two).  `rfl`. -/
theorem monadTailWord_singleBlock :
    blockDecompose involutionMonadSplit monadTailWord = [(false, [tLetter, tLetter])] := rfl

/-- The monad tail's single-block structure derived from the GENERAL block-purity `monoBlockDecompose` (not merely
`rfl`), tying the concrete image to the general reason. -/
theorem monadTailWord_monoBlockGeneral :
    blockDecompose involutionMonadSplit monadTailWord = monoFalseBlocks monadTailWord :=
  monoBlockDecompose involutionMonadSplit monadTailWord monadTailWord_allTwo

/-! ## Observability -/

-- The dispatch routing of the real combined cell `s·t`: expect `[true, false]`.
#eval blockTags involutionMonadSplit crossPairDomainWord
-- The dispatch routing of the alternating witness word `s t s t t`: expect `[true, false, true, false]`.
#eval blockTags involutionMonadSplit witnessWord
-- The dispatch-map image boundary `t·t` decomposed: expect one block `[(false, [1, 1])]`.
#eval (blockDecompose involutionMonadSplit monadTailWord).map (fun block => (block.1, block.2.map Fin.val))

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the block factorization + dispatch map ASSEMBLE, non-vacuously (B1).**  The dispatch
routing map `blockTags` (per-block component schedule) with its soundness (`blockTags_recompose_sound`), the
general block-purity of a dispatch-map image (`monoBlockDecompose`: a mono-component word is a single block, with
`monoBlockDecompose_lengthLeOne`), the dispatch map FIRING on the real monad unit (`dispatchedMonadUnit` /
`dispatchedMonadUnit_isGen` / `dispatchedMonadUnit_index` at index 0), and the non-vacuity CONTRAST — a real
combined cell's boundary `s·t` routes to TWO blocks (`crossPairDomainRouting`, `crossPairDomain_multiBlock`) while a
dispatch-map image's boundary `t·t` routes to ONE (`monadTailWord_singleBlock`, `monadTailWord_monoBlockGeneral`).
The 1-cell substrate the saturated dispatch runs over is present and exercised on a genuinely combined cell.
`= true`. -/
def fxAmalg_hasBlockDispatchMap : Bool := true

end FX1Poly.Polygraph.Amalgam
