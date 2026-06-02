import FX1Poly.OmegacE.IdempotentSystem
import FX1Poly.OmegacE.ReducerNormalizer

/-! # FX1Poly/OmegacE/IdempotentReducer
    — the searchable reducer + terminating normalizer for the idempotent system `[c,c] → [c]`

`IdempotentSystem.lean` shipped the idempotent rule and its TERMINATION (length-reducing).  `ReducerNormalizer`
showed termination + a sound-and-complete `WordReducer` ⟹ a `WordNormalizer` (`toNormalizer`).  This file
supplies that reducer for the idempotent system — the first CONCRETE `WordReducer` on the Path-B leg (the empty
system used the identity normalizer; this is the first one that genuinely rewrites) — and assembles the
**first terminating normalizer for a non-trivial concrete ωcE rewrite system**.

The reducer is the leftmost-redex scan `idempotentReduceCells`: walk the cell list for an adjacent `[c,c]`,
splice it to `[c]`.  Its two correctness obligations:

* `idempotentReduceCells_sound` — a produced reduct is a genuine `RewritesOneStep` (the splice IS a `fire`
  under the surrounding left/right context).
* completeness (`idempotentRewrite_implies_reduceCells_isSome` + the reducer's `reduceOnce_complete`) — a
  `none` result means NO rewrite exists.  This is the structural INVERSION of one-step rewriting for the
  idempotent system: every `RewritesOneStep` (by induction on its `fire`/context derivation) implies the scan
  finds a redex.  The two monotonicity lemmas `idempotentReduceCells_isSome_append_{left,right}` carry "a redex
  survives appending a prefix/suffix" — exactly the `underLeftContext`/`underRightContext` cases.

Then `idempotentWordReducer : WordReducer (idempotentSystem cell)` bundles sound + complete, and
`idempotentWordNormalizer : WordNormalizer (idempotentSystem cell)` is `toNormalizer` applied to the shipped
termination — a real normalizer that iterates `reduceOnce` along the well-founded length measure.

## Honest scope

This is the reducer + normalizer, NOT yet the decidable word problem.  `decidableConvertibleModulo_ofConvergent`
also needs `HasLocalConfluence (idempotentSystem cell)` — the critical-pair check (the unique overlap `[c,c,c]`
reduces to `[c,c]` via BOTH firings, joinable at `[c,c]` by reflexivity; disjoint redexes commute).  That
local-confluence proof — a structural overlap analysis over the three `RewritesOneStep` constructors — is the
final Path-B atom for this concrete system; with it, `newman` + this normalizer decide convertibility.

## Zero-axiom verification

The reducer is structural list recursion; soundness/completeness are inductions over `RewritesOneStep` using
the append-monotonicity lemmas.  Impossible `none = some` / `none.isSome = true` hypotheses are refuted by
`nomatch` / `Bool.noConfusion` (NOT `simp`-to-`True`, which would pull `propext`); the doubled-redex evaluation
uses `dsimp only` + `if_pos ⟨rfl, rfl⟩` (NOT `simp`, which rewrites `c = c` to `True` via `propext`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- Scan a cell list for the leftmost adjacent `[cell, cell]` pair and splice it to `[cell]`; the searchable
one-step rewrite engine for the idempotent system at the list level. -/
def idempotentReduceCells {dimension : Nat} (cell : OmegacECell dimension) :
    List (OmegacECell dimension) → Option (List (OmegacECell dimension))
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if first = cell ∧ second = cell then
        some (cell :: rest)
      else
        (idempotentReduceCells cell (second :: rest)).map (fun reducedTail => first :: reducedTail)

/-- The scan fires on a doubled cell: `[c,c]` reduces to `[c]` (the `fire` base case, evaluated without `simp`
to keep `c = c` from collapsing to `True` via `propext`). -/
theorem idempotentReduceCells_doubled {dimension : Nat} (cell : OmegacECell dimension) :
    idempotentReduceCells cell [cell, cell] = some [cell] := by
  dsimp only [idempotentReduceCells]
  rw [if_pos (And.intro rfl rfl)]

/-- `Option.map` preserves `isSome` (the bridge between the `map`-lifted reducer and its raw search result). -/
theorem option_isSome_map {α β : Type _} (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by
  cases o <;> rfl

/-- **A redex in `xs` survives appending a suffix.**  The `underRightContext` half of the completeness
inversion: if the scan finds a redex in `xs`, it still finds one in `xs ++ ys`. -/
theorem idempotentReduceCells_isSome_append_right {dimension : Nat} (cell : OmegacECell dimension)
    (ys : List (OmegacECell dimension)) :
    ∀ {xs : List (OmegacECell dimension)},
      (idempotentReduceCells cell xs).isSome = true →
      (idempotentReduceCells cell (xs ++ ys)).isSome = true := by
  intro xs
  induction xs with
  | nil => intro hxs; exact Bool.noConfusion hxs
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro hxs; exact Bool.noConfusion hxs
      | cons second rest =>
          intro hxs
          simp only [idempotentReduceCells] at hxs
          rw [List.cons_append, List.cons_append]
          simp only [idempotentReduceCells]
          by_cases hpair : first = cell ∧ second = cell
          · rw [if_pos hpair]; rfl
          · rw [if_neg hpair] at hxs
            rw [if_neg hpair]
            rw [option_isSome_map] at hxs ⊢
            have spliced := ihTail hxs
            rw [List.cons_append] at spliced
            exact spliced

/-- **A redex in `ys` survives appending a prefix.**  The `underLeftContext` half of the completeness
inversion: if the scan finds a redex in `ys`, it still finds one in `xs ++ ys`. -/
theorem idempotentReduceCells_isSome_append_left {dimension : Nat} (cell : OmegacECell dimension) :
    ∀ (xs : List (OmegacECell dimension)) {ys : List (OmegacECell dimension)},
      (idempotentReduceCells cell ys).isSome = true →
      (idempotentReduceCells cell (xs ++ ys)).isSome = true := by
  intro xs
  induction xs with
  | nil => intro ys hys; exact hys
  | cons first xs' ihTail =>
      intro ys hys
      rw [List.cons_append]
      have tail := ihTail hys
      cases hzs : xs' ++ ys with
      | nil => rw [hzs] at tail; exact Bool.noConfusion tail
      | cons second rest =>
          simp only [idempotentReduceCells]
          by_cases hpair : first = cell ∧ second = cell
          · rw [if_pos hpair]; rfl
          · rw [if_neg hpair, option_isSome_map]
            rw [hzs] at tail
            exact tail

/-- **Soundness**: a produced reduct is a genuine one-step rewrite.  By induction on the list: the head splice
is `fire` under the right context (`idempotentRule_fires`); the recursive splice is `underLeftContext` of the
inductive step. -/
theorem idempotentReduceCells_sound {dimension : Nat} (cell : OmegacECell dimension) :
    ∀ {xs ys : List (OmegacECell dimension)},
      idempotentReduceCells cell xs = some ys →
      OmegacEWord.RewritesOneStep (idempotentSystem cell) ⟨xs⟩ ⟨ys⟩ := by
  intro xs
  induction xs with
  | nil => intro ys hred; simp only [idempotentReduceCells] at hred; nomatch hred
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro ys hred; simp only [idempotentReduceCells] at hred; nomatch hred
      | cons second rest =>
          intro ys hred
          simp only [idempotentReduceCells] at hred
          by_cases hpair : first = cell ∧ second = cell
          · rw [if_pos hpair] at hred
            injection hred with hys
            subst hys
            obtain ⟨hFirst, hSecond⟩ := hpair
            rw [hFirst, hSecond]
            exact OmegacEWord.RewritesOneStep.underRightContext ⟨rest⟩ (idempotentRule_fires cell)
          · rw [if_neg hpair] at hred
            cases hinner : idempotentReduceCells cell (second :: rest) with
            | none =>
                rw [hinner] at hred
                simp only [Option.map_none] at hred
                nomatch hred
            | some zs =>
                rw [hinner] at hred
                simp only [Option.map_some] at hred
                injection hred with hys
                subst hys
                exact OmegacEWord.RewritesOneStep.underLeftContext ⟨[first]⟩ (ihTail hinner)

/-- **Completeness core**: a one-step rewrite means the scan finds a redex.  By induction on the rewrite
derivation: `fire` lands on a doubled cell; the context cases route through the append-monotonicity lemmas. -/
theorem idempotentRewrite_implies_reduceCells_isSome {dimension : Nat}
    (cell : OmegacECell dimension) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (idempotentSystem cell) source target →
      (idempotentReduceCells cell source.cells).isSome = true := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      have ruleEq : rule = idempotentRule cell := isInSystem
      subst ruleEq
      show (idempotentReduceCells cell [cell, cell]).isSome = true
      rw [idempotentReduceCells_doubled]
      rfl
  | underLeftContext prefixWord _inner innerIH =>
      exact idempotentReduceCells_isSome_append_left cell prefixWord.cells innerIH
  | underRightContext suffixWord _inner innerIH =>
      exact idempotentReduceCells_isSome_append_right cell suffixWord.cells innerIH

/-- Lift the cell-list scan to a word-level reducer. -/
def idempotentReduceOnce {dimension : Nat} (cell : OmegacECell dimension)
    (word : OmegacEWord dimension) : Option (OmegacEWord dimension) :=
  (idempotentReduceCells cell word.cells).map (fun reducedCells => { cells := reducedCells })

/-- **The sound + complete reducer for the idempotent system** — the first concrete `WordReducer` on the
Path-B leg that genuinely rewrites (the empty system's reducer was the identity). -/
def idempotentWordReducer {dimension : Nat} (cell : OmegacECell dimension) :
    WordReducer (idempotentSystem cell) where
  reduceOnce := idempotentReduceOnce cell
  reduceOnce_sound := by
    intro word reduct hred
    simp only [idempotentReduceOnce] at hred
    cases hcells : idempotentReduceCells cell word.cells with
    | none =>
        rw [hcells] at hred
        simp only [Option.map_none] at hred
        nomatch hred
    | some ys =>
        rw [hcells] at hred
        simp only [Option.map_some] at hred
        injection hred with hreduct
        subst hreduct
        exact idempotentReduceCells_sound cell hcells
  reduceOnce_complete := by
    intro word hnone reduct step
    have isSome := idempotentRewrite_implies_reduceCells_isSome cell step
    simp only [idempotentReduceOnce] at hnone
    cases hcells : idempotentReduceCells cell word.cells with
    | none => rw [hcells] at isSome; exact Bool.noConfusion isSome
    | some ys =>
        rw [hcells] at hnone
        simp only [Option.map_some] at hnone
        nomatch hnone

/-- **The terminating normalizer for the idempotent system** — `toNormalizer` of the reducer along the shipped
length-measure termination.  The first terminating normalizer for a non-trivial concrete ωcE rewrite system. -/
def idempotentWordNormalizer {dimension : Nat} (cell : OmegacECell dimension) :
    WordNormalizer (idempotentSystem cell) :=
  (idempotentWordReducer cell).toNormalizer (idempotentSystem_isTerminating cell)

end FX1Poly.OmegacE
