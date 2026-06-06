import FX1Poly.OmegacE.TranspositionConfluence
import FX1Poly.OmegacE.IdempotentReducer

/-!
# Bounded-search decidability for the transposition word system

This is the FINAL atom of the transposition system: the executable normalizer + the
decidable word problem for the length-PRESERVING adjacent-transposition system
`[firstCell, secondCell] -> [secondCell, firstCell]`.

The shape mirrors `IdempotentReducer.lean` exactly — the only mathematical
difference is the rule (a length-preserving swap, not a length-reducing
collapse).  A `WordReducer` bundles a leftmost-redex scanner with soundness and
completeness; `decidableConvertibleModulo_ofConvergent` then turns
local confluence (`transpositionHasLocalConfluence`) plus termination
(`transpositionSystem_isTerminating`) plus this reducer into a parameter-free
`Decidable (ConvertibleModulo …)` instance.

Convergence here is genuine Newman: the system is NOT length-reducing (a swap
keeps `|word|` fixed), so termination is carried by the inversion-count measure
`aBeforeBInversions` shipped in `TranspositionSystem.lean`, and local
confluence is the orthogonal-redex critical-pair analysis in
`TranspositionConfluence.lean`.  The Leg-3 (Makkai/Forest) word-problem
demonstration is thereby decided for a non-trivial convergent presentation.

Propext discipline (matches the gated idempotent template): `nomatch` /
`Bool.noConfusion` instead of simp-to-`True`; `dsimp only` + `if_pos ⟨rfl, rfl⟩`
for the firing equation; `simp only [<def>]` only ever unfolds the scanner's own
equations (never list-append lemmas, whose simp machinery leaks propext); the
generic `option_isSome_map` is reused from `IdempotentReducer.lean`.

All declarations are gated by per-decl `#assert_no_axioms` in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- Leftmost-redex scanner for the transposition rule.  Walks the cell list and,
at the first adjacent `[firstCell, secondCell]` pair, splices it to
`[secondCell, firstCell]`, leaving the suffix untouched; recurses into the tail
otherwise.  `none` exactly when no such adjacency exists. -/
def transpositionReduceCells {dimension : Nat} (firstCell secondCell : OmegacECell dimension) :
    List (OmegacECell dimension) → Option (List (OmegacECell dimension))
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if first = firstCell ∧ second = secondCell then
        some (secondCell :: firstCell :: rest)
      else
        (transpositionReduceCells firstCell secondCell (second :: rest)).map
          (fun reducedTail => first :: reducedTail)

/-- The scanner fires on the bare redex `[firstCell, secondCell]`, producing the
swapped pair.  Analogue of `idempotentReduceCells_doubled`. -/
theorem transpositionReduceCells_fires {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) :
    transpositionReduceCells firstCell secondCell [firstCell, secondCell]
      = some [secondCell, firstCell] := by
  dsimp only [transpositionReduceCells]
  rw [if_pos (And.intro rfl rfl)]

/-- Monotonicity under a right context: if the scanner fires on `xs`, it fires on
`xs ++ ys`.  This is the `underRightContext` completeness half. -/
theorem transpositionReduceCells_isSome_append_right {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) (ys : List (OmegacECell dimension)) :
    ∀ {xs : List (OmegacECell dimension)},
      (transpositionReduceCells firstCell secondCell xs).isSome = true →
      (transpositionReduceCells firstCell secondCell (xs ++ ys)).isSome = true := by
  intro xs
  induction xs with
  | nil => intro hxs; exact Bool.noConfusion hxs
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro hxs; exact Bool.noConfusion hxs
      | cons second rest =>
          intro hxs
          simp only [transpositionReduceCells] at hxs
          rw [List.cons_append, List.cons_append]
          simp only [transpositionReduceCells]
          by_cases hpair : first = firstCell ∧ second = secondCell
          · rw [if_pos hpair]; rfl
          · rw [if_neg hpair] at hxs
            rw [if_neg hpair]
            rw [option_isSome_map] at hxs ⊢
            have spliced := ihTail hxs
            rw [List.cons_append] at spliced
            exact spliced

/-- Monotonicity under a left context: if the scanner fires on `ys`, it fires on
`xs ++ ys`.  This is the `underLeftContext` completeness half. -/
theorem transpositionReduceCells_isSome_append_left {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) :
    ∀ (xs : List (OmegacECell dimension)) {ys : List (OmegacECell dimension)},
      (transpositionReduceCells firstCell secondCell ys).isSome = true →
      (transpositionReduceCells firstCell secondCell (xs ++ ys)).isSome = true := by
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
          simp only [transpositionReduceCells]
          by_cases hpair : first = firstCell ∧ second = secondCell
          · rw [if_pos hpair]; rfl
          · rw [if_neg hpair, option_isSome_map]
            rw [hzs] at tail
            exact tail

/-- Soundness: any reduct the scanner produces is reachable by a single
transposition rewrite.  The head splice is a `fire` under a right context; the
recursive descent is `underLeftContext` with the singleton prefix `[first]`. -/
theorem transpositionReduceCells_sound {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) :
    ∀ {xs ys : List (OmegacECell dimension)},
      transpositionReduceCells firstCell secondCell xs = some ys →
      OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell) ⟨xs⟩ ⟨ys⟩ := by
  intro xs
  induction xs with
  | nil => intro ys hred; simp only [transpositionReduceCells] at hred; nomatch hred
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro ys hred; simp only [transpositionReduceCells] at hred; nomatch hred
      | cons second rest =>
          intro ys hred
          simp only [transpositionReduceCells] at hred
          by_cases hpair : first = firstCell ∧ second = secondCell
          · rw [if_pos hpair] at hred
            injection hred with hys
            subst hys
            obtain ⟨hFirst, hSecond⟩ := hpair
            rw [hFirst, hSecond]
            exact OmegacEWord.RewritesOneStep.underRightContext ⟨rest⟩
              (transpositionRule_fires firstCell secondCell)
          · rw [if_neg hpair] at hred
            cases hinner : transpositionReduceCells firstCell secondCell (second :: rest) with
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

/-- Completeness core: whenever the system can take a step from `source`, the
scanner fires on `source.cells`.  By induction on the rewrite derivation —
`fire` lands on the bare redex (`transpositionReduceCells_fires`), the context
cases reuse the two monotonicity lemmas. -/
theorem transpositionRewrite_implies_reduceCells_isSome {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell) source target →
      (transpositionReduceCells firstCell secondCell source.cells).isSome = true := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      have ruleEq : rule = transpositionRule firstCell secondCell := isInSystem
      subst ruleEq
      show (transpositionReduceCells firstCell secondCell [firstCell, secondCell]).isSome = true
      rw [transpositionReduceCells_fires]
      rfl
  | underLeftContext prefixWord _inner innerIH =>
      exact transpositionReduceCells_isSome_append_left firstCell secondCell prefixWord.cells innerIH
  | underRightContext suffixWord _inner innerIH =>
      exact transpositionReduceCells_isSome_append_right firstCell secondCell suffixWord.cells innerIH

/-- Word-level wrapper: lift the cell scanner to words. -/
def transpositionReduceOnce {dimension : Nat} (firstCell secondCell : OmegacECell dimension)
    (word : OmegacEWord dimension) : Option (OmegacEWord dimension) :=
  (transpositionReduceCells firstCell secondCell word.cells).map (fun reducedCells => { cells := reducedCells })

/-- The bundled reducer: leftmost-redex scanner with soundness + completeness.
Note: this object needs NO distinctness hypothesis — soundness and completeness
hold for any pair (even `firstCell = secondCell`, where the system is merely
non-terminating, which only the decidability capstone below needs to exclude). -/
def transpositionWordReducer {dimension : Nat} (firstCell secondCell : OmegacECell dimension) :
    WordReducer (transpositionSystem firstCell secondCell) where
  reduceOnce := transpositionReduceOnce firstCell secondCell
  reduceOnce_sound := by
    intro word reduct hred
    simp only [transpositionReduceOnce] at hred
    cases hcells : transpositionReduceCells firstCell secondCell word.cells with
    | none =>
        rw [hcells] at hred
        simp only [Option.map_none] at hred
        nomatch hred
    | some ys =>
        rw [hcells] at hred
        simp only [Option.map_some] at hred
        injection hred with hreduct
        subst hreduct
        exact transpositionReduceCells_sound firstCell secondCell hcells
  reduceOnce_complete := by
    intro word hnone reduct step
    have isSome := transpositionRewrite_implies_reduceCells_isSome firstCell secondCell step
    simp only [transpositionReduceOnce] at hnone
    cases hcells : transpositionReduceCells firstCell secondCell word.cells with
    | none => rw [hcells] at isSome; exact Bool.noConfusion isSome
    | some ys =>
        rw [hcells] at hnone
        simp only [Option.map_some] at hnone
        nomatch hnone

/-- **The transposition-system capstone.**  The word problem for the length-preserving
transposition system is decidable.  Convergence = local confluence
(`transpositionHasLocalConfluence`, orthogonal critical pairs) + termination
(`transpositionSystem_isTerminating`, inversion-count measure), fed through
`decidableConvertibleModulo_ofConvergent` with this bounded-search reducer.
The distinctness hypothesis `firstCell ≠ secondCell` is exactly what makes the
swap strictly decrease the inversion count, hence terminate. -/
def decidableConvertibleModulo_transpositionSystem {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) (distinct : firstCell ≠ secondCell)
    (firstWord secondWord : OmegacEWord dimension) :
    Decidable (OmegacEWord.ConvertibleModulo (transpositionSystem firstCell secondCell)
      firstWord secondWord) :=
  decidableConvertibleModulo_ofConvergent
    (transpositionHasLocalConfluence firstCell secondCell distinct)
    (transpositionSystem_isTerminating firstCell secondCell distinct)
    (transpositionWordReducer firstCell secondCell) firstWord secondWord

end FX1Poly.OmegacE
