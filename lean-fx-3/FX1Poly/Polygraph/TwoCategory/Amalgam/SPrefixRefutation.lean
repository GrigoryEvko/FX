import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/SPrefixRefutation — the s-prefix normal form is UNREACHABLE (WP-AMALG-2 r3, B1)

The r3 recon proposed a candidate pushout normal form: "commute every involution atom `s` to a PREFIX; the
involution is 1-cell-thin, so its 2-whiskers bubble past the monad 2-cells freely, yielding an `s`-prefix form
`whiskerLeft (s-word) (pure monad cell)`."  This file REFUTES that candidate, machine-checked, with the exact
non-commuting word.

## The obstruction (the free monoid on `{s, t}` does not commute)

The shipped free-cross-component commutation `crossComponentWhiskerCommute` (`DispatchSaturated.lean`) only
RE-NESTS a left-`s`-whisker and a right-`t`-whisker of a SINGLE body (`s ◁ (_ ▷ t) ≈ (s ◁ _) ▷ t`, the Godement /
middle-four exchange).  It does NOT reposition an `s` sitting to the RIGHT of a `t`: to pull the `s` out of the
context `t·s` into a prefix one would need `t·s ≈ s·t` as 1-CELLS, which is FALSE in the free monoid on the
disjoint generators.  A `SaturatedConvOver` fixes the boundary 1-cells, so a cell whose domain word is `t·s`
cannot be convertible to any `s`-prefix-form cell (whose domain word necessarily starts with an involution
block).  The `s`-prefix NF is therefore unreachable; the correct NF is GAP-indexed (`PushoutNormalForm.lean`).

## What is shipped here (each zero-axiom, structural / `decide`, ASCII-only, computes under `#eval`)

  * **`crossPairTSWord`** — the exact non-commuting word `t·s` over the pushout alphabet.
  * **`crossPairTSWord_blockDecompose`** — it factors into `[(t), (s)]` (`rfl`): the involution block is NON-initial.
  * **`crossPairSTWord_blockDecompose`** — its `s`-to-front reordering `s·t` factors into `[(s), (t)]`, the
    `s`-prefix shape — a DIFFERENT word (`crossPairTSWord_ne_STWord`), so commuting changes the 1-cell boundary.
  * **`hasSPrefixSplit`** — the predicate "the word splits as (all-component-1 prefix) ++ (all-component-2 suffix)".
  * **`crossPairTSWord_not_sPrefixForm`** — the REFUTATION: `t·s` has NO such split (the exact non-commuting word).
  * **`crossPairTSIdentityCell`** — a genuine pushout 2-cell realizing the `t·s` boundary (non-vacuity anchor).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The exact non-commuting word `t·s` and its `s`-to-front reordering -/

/-- ★ **The exact non-commuting word** — `t·s` over the pushout alphabet, a component-2 letter FOLLOWED by a
component-1 letter.  The `s` sits to the RIGHT of the `t`, so it cannot be commuted to a prefix without changing
the 1-cell. -/
def crossPairTSWord : List (Fin involutionMonadPushout.modalityGenerators.length) :=
  [tLetter, sLetter]

/-- The `s`-to-front reordering `s·t` — the `s`-prefix shape the refuted NF candidate would demand. -/
def crossPairSTWord : List (Fin involutionMonadPushout.modalityGenerators.length) :=
  [sLetter, tLetter]

/-- ★ **`t·s` factors with the involution block NON-INITIAL** — `blockDecompose` yields `[(false, [t]), (true,
[s])]` (`rfl`): the component-2 `t`-block leads, the component-1 `s`-block trails.  Not an `s`-prefix form. -/
theorem crossPairTSWord_blockDecompose :
    blockDecompose involutionMonadSplit crossPairTSWord = [(false, [tLetter]), (true, [sLetter])] := rfl

/-- ★ **`s·t` factors with the involution block INITIAL** — `blockDecompose` yields `[(true, [s]), (false, [t])]`
(`rfl`): the `s`-prefix shape.  This is the reordering the candidate NF wants, but it is a DIFFERENT word. -/
theorem crossPairSTWord_blockDecompose :
    blockDecompose involutionMonadSplit crossPairSTWord = [(true, [sLetter]), (false, [tLetter])] := rfl

/-- ★ **The reordering CHANGES the word** — `t·s ≠ s·t` (the letters differ, `t.val = 1 ≠ 0 = s.val`).  So moving
the `s` to the front is not a boundary-preserving operation: no `SaturatedConvOver` (which fixes the boundary
1-cell) can realize it. -/
theorem crossPairTSWord_ne_STWord : crossPairTSWord ≠ crossPairSTWord := by decide

/-! ## The `s`-prefix form predicate and its refutation on `t·s` -/

/-- Whether a word is entirely component-1 (all letters `s`, tag `true`). -/
def isAllComponentOne (word : List (Fin involutionMonadPushout.modalityGenerators.length)) : Bool :=
  word.all (fun letter => letterTag involutionMonadSplit letter)

/-- Whether a word is entirely component-2 (all letters `t`, tag `false`). -/
def isAllComponentTwo (word : List (Fin involutionMonadPushout.modalityGenerators.length)) : Bool :=
  word.all (fun letter => not (letterTag involutionMonadSplit letter))

/-- The **`s`-prefix normal form** predicate — the word splits as (all-component-1 prefix) ++ (all-component-2
suffix).  This is exactly the boundary shape a cell `whiskerLeft (s-word) (pure monad cell)` presents (its domain
word is an all-`s` prefix followed by an all-`t` monad suffix). -/
def hasSPrefixSplit (word : List (Fin involutionMonadPushout.modalityGenerators.length)) : Prop :=
  ∃ prefixWord suffixWord, word = prefixWord ++ suffixWord
    ∧ isAllComponentOne prefixWord = true ∧ isAllComponentTwo suffixWord = true

/-- ★★ **THE REFUTATION (B1).**  The word `t·s` has NO `s`-prefix split — every candidate split fails a component
purity check: an empty prefix leaves the suffix `t·s`, which is not all-component-2 (`s` is component-1); a
non-empty prefix starts with `t`, which is not component-1.  Hence the `s`-prefix normal form is UNREACHABLE for
this boundary — the machine-checked counterexample to the candidate NF, with the exact non-commuting word. -/
theorem crossPairTSWord_not_sPrefixForm : ¬ hasSPrefixSplit crossPairTSWord := by
  rintro ⟨prefixWord, suffixWord, heq, hprefix, hsuffix⟩
  cases prefixWord with
  | nil =>
      rw [List.nil_append] at heq
      rw [← heq] at hsuffix
      exact absurd hsuffix (by decide)
  | cons headLetter restPrefix =>
      simp only [crossPairTSWord, List.cons_append] at heq
      injection heq with hhead _htail
      rw [← hhead] at hprefix
      simp only [isAllComponentOne, List.all_cons] at hprefix
      have htag : letterTag involutionMonadSplit tLetter = false := by decide
      rw [htag, Bool.false_and] at hprefix
      exact Bool.noConfusion hprefix

/-! ## Non-vacuity: a genuine pushout 2-cell realizes the `t·s` boundary -/

/-- The `t·s` boundary path over the pushout (a component-2 `t` then a component-1 `s`). -/
def crossPairTSPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  composePath monadPushTPath monadPushSPath

/-- ★ **A genuine pushout 2-cell with domain word `t·s`** — the identity on the `t·s` path anchors the refutation:
the boundary `t·s` is realized by a real free 2-cell, so `crossPairTSWord_not_sPrefixForm` is non-vacuous. -/
def crossPairTSIdentityCell :
    RawTwoCellExpr involutionMonadPushout.toModeSignature crossPairTSPath crossPairTSPath :=
  RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) crossPairTSPath

/-! ## Observability -/

-- The `t·s` decomposition: expect `[(false, [1]), (true, [0])]` (t @ 1 leads, s @ 0 trails).
#eval (blockDecompose involutionMonadSplit crossPairTSWord).map (fun block => (block.1, block.2.map Fin.val))
-- Its `s`-to-front reordering: expect `[(true, [0]), (false, [1])]` — a DIFFERENT word.
#eval (blockDecompose involutionMonadSplit crossPairSTWord).map (fun block => (block.1, block.2.map Fin.val))
-- The suffix `t·s` is not all-component-2: expect `false`.
#eval isAllComponentTwo crossPairTSWord
-- The two words differ: expect `true`.
#eval decide (crossPairTSWord ≠ crossPairSTWord)

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the `s`-prefix normal form is REFUTED (WP-AMALG-2 r3, B1).**  `= true`: the recon's
candidate NF ("commute all involution atoms to a prefix") is machine-checked FALSE.  The exact non-commuting word
`crossPairTSWord = t·s` factors with the involution block NON-initial (`crossPairTSWord_blockDecompose`), its
`s`-to-front reordering is a DIFFERENT word (`crossPairTSWord_ne_STWord`, so the move is not boundary-preserving),
and `t·s` admits NO `s`-prefix split (`crossPairTSWord_not_sPrefixForm`).  The `s`-whiskers are pinned by the
non-commutative free monoid on the disjoint generators — the shipped `crossComponentWhiskerCommute` only re-nests
disjoint whiskers, it does not reposition `s` past `t`.  A genuine pushout 2-cell realizes the `t·s` boundary
(`crossPairTSIdentityCell`), so the refutation is non-vacuous.  The correct NF is GAP-indexed
(`PushoutNormalForm.lean`), NOT `s`-prefixed.  A refutation is a full deliverable.  `= true`. -/
def fxAmalg_sPrefixNormalFormRefuted : Bool := true

end FX1Poly.Polygraph.Amalgam
