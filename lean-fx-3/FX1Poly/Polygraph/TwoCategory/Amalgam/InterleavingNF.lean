import FX1Poly.Polygraph.TwoCategory.Amalgam.Pushout

/-! # Polygraph/TwoCategory/Amalgam/InterleavingNF — the free-product interleaving normal form at 1-cells

The 1-cells of the mode-signature pushout `comp1 +_M comp2` (`Pushout.lean`) are WORDS over the tagged
generator sum: `List (Fin (combinedModalityGenerators …).length)`, each letter tagged by its component (index
`< len1` = component 1, `≥ len1` = component 2).  The classical FREE-PRODUCT NORMAL FORM (Nyberg-Brodda,
"On the Word Problem for Free Products of Semigroups and Monoids", Lemma 1.1 / 1.2; the "alternating product"
of Wikipedia's *Free product*) factors every such word UNIQUELY into maximal same-component blocks whose tags
ALTERNATE.  This file makes that factorisation constructive.

## What is shipped here (each piece zero-axiom, structural, ASCII-only, computes under `#eval`)

  * **`letterTag`** — the component tag of a letter (`Nat.blt letter.val splitPoint`; `splitPoint = len1`).
  * **`blockDecompose`** — the alternating factorisation: structural on the word, merging each head letter into
    the leading block when tags agree, opening a fresh block when they differ.
  * **`recompose`** — concatenate the blocks' letter-lists back into a flat word.
  * **`blockDecompose_sound`** — `recompose (blockDecompose word) = word` (the factorisation loses nothing).
  * **`isAlternating`** + **`blockDecompose_alternates`** — adjacent blocks carry DIFFERENT tags (the "reduced"
    / alternation invariant of the free-product NF).
  * **`blockDecompose_blocksNonempty`** — every block is non-degenerate (non-empty letter list).

Together these are the constructive content of "a pushout word = a unique alternating product of factor
blocks".  Cross-component 2-cell interaction (the DISPATCH layer) reduces to block-wise dispatch over exactly
this factorisation.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

/-! ## Tags and blocks -/

/-- The **component tag** of a pushout-word letter — `true` for component 1 (index `< splitPoint`, where
`splitPoint = len1`), `false` for component 2.  A pure `Bool` (`Nat.blt`), so it computes. -/
def letterTag (splitPoint : Nat) {bound : Nat} (letter : Fin bound) : Bool :=
  Nat.blt letter.val splitPoint

/-- A **tagged block** — a component tag paired with the block's letters. -/
abbrev TaggedBlock (bound : Nat) : Type := Bool × List (Fin bound)

/-- Whether two tags DIFFER — the adjacency test for the alternation invariant (full four-case, propext-free). -/
def tagsDiffer : Bool → Bool → Bool
  | true, false => true
  | false, true => true
  | true, true => false
  | false, false => false

/-! ## The alternating factorisation -/

/-- Prepend a letter to an already-decomposed suffix: merge into the leading block when the tags agree, open a
fresh singleton block when they differ.  Full four-case Bool match — propext-free. -/
def prependLetter (splitPoint : Nat) {bound : Nat} (letter : Fin bound)
    (blocks : List (TaggedBlock bound)) : List (TaggedBlock bound) :=
  match blocks with
  | [] => [(letterTag splitPoint letter, [letter])]
  | (headTag, headLetters) :: moreBlocks =>
      match letterTag splitPoint letter, headTag with
      | true, true => (true, letter :: headLetters) :: moreBlocks
      | false, false => (false, letter :: headLetters) :: moreBlocks
      | true, false => (true, [letter]) :: (false, headLetters) :: moreBlocks
      | false, true => (false, [letter]) :: (true, headLetters) :: moreBlocks

/-- ★ The **alternating factorisation** — decompose a pushout word into maximal same-component blocks.
Structural on the word (peel head, `prependLetter` into the decomposed tail). -/
def blockDecompose (splitPoint : Nat) {bound : Nat} : List (Fin bound) → List (TaggedBlock bound)
  | [] => []
  | letter :: rest => prependLetter splitPoint letter (blockDecompose splitPoint rest)

/-- Concatenate the blocks' letter-lists back into a flat word (the inverse of `blockDecompose`). -/
def recompose {bound : Nat} : List (TaggedBlock bound) → List (Fin bound)
  | [] => []
  | (_, letters) :: more => letters ++ recompose more

/-! ## Soundness: recomposing recovers the word -/

/-- `prependLetter` prepends exactly the letter under `recompose` (the four Bool cases collapse via
`List.cons_append` / `List.nil_append`, both definitional). -/
theorem prependLetter_recompose (splitPoint : Nat) {bound : Nat} (letter : Fin bound)
    (blocks : List (TaggedBlock bound)) :
    recompose (prependLetter splitPoint letter blocks) = letter :: recompose blocks := by
  cases blocks with
  | nil => rfl
  | cons headBlock moreBlocks =>
      obtain ⟨headTag, headLetters⟩ := headBlock
      cases headTag <;>
        (cases hLetterTag : letterTag splitPoint letter <;>
          simp only [prependLetter, hLetterTag, recompose] <;> rfl)

/-- ★ **Soundness** — the alternating factorisation loses nothing: recomposing recovers the original word. -/
theorem blockDecompose_sound (splitPoint : Nat) {bound : Nat} (word : List (Fin bound)) :
    recompose (blockDecompose splitPoint word) = word := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      show recompose (prependLetter splitPoint letter (blockDecompose splitPoint rest)) = letter :: rest
      rw [prependLetter_recompose, ih]

/-! ## The alternation invariant -/

/-- Whether a block list is ALTERNATING — adjacent blocks carry differing tags (structural on the list). -/
def isAlternating {bound : Nat} : List (TaggedBlock bound) → Bool
  | [] => true
  | [_] => true
  | blockA :: blockB :: more => tagsDiffer blockA.1 blockB.1 && isAlternating (blockB :: more)

/-- Replacing a leading block's LETTERS (not its tag) leaves the alternation verdict unchanged — `isAlternating`
inspects only tags and the tail. -/
theorem isAlternating_headLettersIrrelevant {bound : Nat} (tag : Bool)
    (lettersOne lettersTwo : List (Fin bound)) (moreBlocks : List (TaggedBlock bound)) :
    isAlternating ((tag, lettersOne) :: moreBlocks) = isAlternating ((tag, lettersTwo) :: moreBlocks) := by
  cases moreBlocks with
  | nil => rfl
  | cons _ _ => rfl

/-- `prependLetter` preserves the alternation invariant (the merge keeps the head tag; the open inserts a fresh
tag that differs from the old head). -/
theorem prependLetter_preserves_alternating (splitPoint : Nat) {bound : Nat} (letter : Fin bound)
    (blocks : List (TaggedBlock bound)) (alt : isAlternating blocks = true) :
    isAlternating (prependLetter splitPoint letter blocks) = true := by
  cases blocks with
  | nil => rfl
  | cons headBlock moreBlocks =>
      obtain ⟨headTag, headLetters⟩ := headBlock
      cases headTag
      · cases hLetterTag : letterTag splitPoint letter
        · -- head component 2, letter component 2: merge (tag unchanged)
          simp only [prependLetter, hLetterTag]
          rw [isAlternating_headLettersIrrelevant false (letter :: headLetters) headLetters moreBlocks]
          exact alt
        · -- head component 2, letter component 1: open (fresh differing tag)
          simp only [prependLetter, hLetterTag, isAlternating, tagsDiffer]
          rw [alt]; rfl
      · cases hLetterTag : letterTag splitPoint letter
        · -- head component 1, letter component 2: open (fresh differing tag)
          simp only [prependLetter, hLetterTag, isAlternating, tagsDiffer]
          rw [alt]; rfl
        · -- head component 1, letter component 1: merge (tag unchanged)
          simp only [prependLetter, hLetterTag]
          rw [isAlternating_headLettersIrrelevant true (letter :: headLetters) headLetters moreBlocks]
          exact alt

/-- ★ **Alternation** — the alternating factorisation is genuinely alternating: adjacent blocks differ in tag. -/
theorem blockDecompose_alternates (splitPoint : Nat) {bound : Nat} (word : List (Fin bound)) :
    isAlternating (blockDecompose splitPoint word) = true := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      show isAlternating (prependLetter splitPoint letter (blockDecompose splitPoint rest)) = true
      exact prependLetter_preserves_alternating splitPoint letter (blockDecompose splitPoint rest) ih

/-! ## Non-degeneracy: every block is non-empty -/

/-- Whether every block in a list has a non-empty letter list (the free-product NF's non-degeneracy). -/
def allBlocksNonempty {bound : Nat} : List (TaggedBlock bound) → Bool
  | [] => true
  | (_, letters) :: more =>
      match letters with
      | [] => false
      | _ :: _ => allBlocksNonempty more

/-- A block list with a non-empty leading block passes non-degeneracy iff its tail does. -/
theorem allBlocksNonempty_tail {bound : Nat} (tag : Bool) (letters : List (Fin bound))
    (moreBlocks : List (TaggedBlock bound))
    (nonempty : allBlocksNonempty ((tag, letters) :: moreBlocks) = true) :
    allBlocksNonempty moreBlocks = true := by
  cases letters with
  | nil => simp only [allBlocksNonempty] at nonempty; exact Bool.noConfusion nonempty
  | cons _ _ => exact nonempty

/-- `prependLetter` keeps all blocks non-empty (the merge grows a block; the open creates a singleton). -/
theorem prependLetter_preserves_nonempty (splitPoint : Nat) {bound : Nat} (letter : Fin bound)
    (blocks : List (TaggedBlock bound)) (nonempty : allBlocksNonempty blocks = true) :
    allBlocksNonempty (prependLetter splitPoint letter blocks) = true := by
  cases blocks with
  | nil => rfl
  | cons headBlock moreBlocks =>
      obtain ⟨headTag, headLetters⟩ := headBlock
      cases headTag
      · cases hLetterTag : letterTag splitPoint letter
        · -- merge component 2
          simp only [prependLetter, hLetterTag, allBlocksNonempty]
          exact allBlocksNonempty_tail false headLetters moreBlocks nonempty
        · -- open before component 2
          simp only [prependLetter, hLetterTag, allBlocksNonempty]
          exact nonempty
      · cases hLetterTag : letterTag splitPoint letter
        · -- open before component 1
          simp only [prependLetter, hLetterTag, allBlocksNonempty]
          exact nonempty
        · -- merge component 1
          simp only [prependLetter, hLetterTag, allBlocksNonempty]
          exact allBlocksNonempty_tail true headLetters moreBlocks nonempty

/-- ★ **Non-degeneracy** — every block of the factorisation is non-empty. -/
theorem blockDecompose_blocksNonempty (splitPoint : Nat) {bound : Nat} (word : List (Fin bound)) :
    allBlocksNonempty (blockDecompose splitPoint word) = true := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      show allBlocksNonempty (prependLetter splitPoint letter (blockDecompose splitPoint rest)) = true
      exact prependLetter_preserves_nonempty splitPoint letter (blockDecompose splitPoint rest) ih

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the free-product interleaving normal form at 1-cells SHIPS.**  `blockDecompose` (the
alternating factorisation), `blockDecompose_sound` (recompose = id), `blockDecompose_alternates` (adjacent
blocks differ in tag), and `blockDecompose_blocksNonempty` (non-degenerate blocks).  This is the constructive
free-product / alternating normal form (Nyberg-Brodda Lemma 1.1/1.2).  `= true`. -/
def fxAmalg_hasInterleavingNF : Bool := true

end FX1Poly.Polygraph.Amalgam
