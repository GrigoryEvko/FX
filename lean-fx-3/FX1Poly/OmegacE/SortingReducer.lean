import FX1Poly.OmegacE.SortingConfluence
import FX1Poly.OmegacE.IdempotentReducer

/-! # FX1Poly/OmegacE/SortingReducer
    — the bounded-search reducer + decidable word problem for the sorting/symmetric system (SN-120 capstone, #623)

This is the FINAL atom of SN-120: the executable normalizer + the decidable word problem for the guarded
sorting / symmetric-group (bubble-sort) system `[a,b] → [b,a]` when `slotValue b < slotValue a`.

The shape mirrors `TranspositionReducer.lean` / `IdempotentReducer.lean`.  The one structural difference is the
scanner's firing test: instead of a fixed-pair equality `first = firstCell ∧ second = secondCell` (a DecidableEq
on cells), the sorting scanner fires on a DECIDABLE ORDER GUARD `slotValue second < slotValue first` (an adjacent
descending pair) — decidable via `Nat.decLt`, so `by_cases`/`if_pos`/`if_neg` work exactly as before.  And the
capstone `decidableConvertibleModulo_sortingSystem` needs NO distinctness hypothesis: the strict-order guard is
baked into the rule family's membership, so termination holds unconditionally (vs transposition, which needed
`firstCell ≠ secondCell` to make the swap strictly decrease the inversion count).

* `sortingReduceCells` — the leftmost descending-adjacency scanner.
* `sortingReduceCells_fires` — fires on a bare descending redex `[bigger, smaller]` (`if_pos descending`).
* `sortingReduceCells_isSome_append_{right,left}` — the two monotonicity halves (reusing `option_isSome_map`).
* `sortingReduceCells_sound` — a produced reduct is a genuine single sorting rewrite (head splice = `fire` of the
  guarded family member `sortingSwapRule_fires` under the right context; recursion = `underLeftContext`).
* `sortingRewrite_implies_reduceCells_isSome` — completeness (induction on the step; `fire` destructures the
  guarded existential membership).
* `sortingWordReducer` — the bundled `WordReducer` (no distinctness).
* `decidableConvertibleModulo_sortingSystem` — THE SN-120 CAPSTONE: convergence (`sortingHasLocalConfluence` +
  `sortingSystem_isTerminating`) + this reducer, fed through `decidableConvertibleModulo_ofConvergent`.  The
  sorting / symmetric-group presentation — the "graduation" of the OmegacE sequence — is fully decided.

## Zero-axiom verification

Mirrors the transposition reducer's propext discipline exactly: `nomatch` / `Bool.noConfusion` (not simp-to-`True`),
`dsimp only` + `if_pos descending` for the firing equation, `simp only [<scanner-def>]` only ever unfolding the
scanner's own equations (never list-append lemmas).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- Leftmost descending-adjacency scanner for the sorting system: at the first pair `[first, second]` with
`slotValue second < slotValue first`, swap to `[second, first]`; recurse into the tail otherwise. -/
def sortingReduceCells {dimension : Nat} (slotValue : OmegacECell dimension → Nat) :
    List (OmegacECell dimension) → Option (List (OmegacECell dimension))
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if slotValue second < slotValue first then
        some (second :: first :: rest)
      else
        (sortingReduceCells slotValue (second :: rest)).map (fun reducedTail => first :: reducedTail)

/-- The scanner fires on a bare descending redex `[bigger, smaller]`, producing the swapped pair. -/
theorem sortingReduceCells_fires {dimension : Nat} (slotValue : OmegacECell dimension → Nat)
    (biggerCell smallerCell : OmegacECell dimension)
    (descending : slotValue smallerCell < slotValue biggerCell) :
    sortingReduceCells slotValue [biggerCell, smallerCell] = some [smallerCell, biggerCell] := by
  dsimp only [sortingReduceCells]
  rw [if_pos descending]

/-- Monotonicity under a right context: if the scanner fires on `xs`, it fires on `xs ++ ys`. -/
theorem sortingReduceCells_isSome_append_right {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) (ys : List (OmegacECell dimension)) :
    ∀ {xs : List (OmegacECell dimension)},
      (sortingReduceCells slotValue xs).isSome = true →
      (sortingReduceCells slotValue (xs ++ ys)).isSome = true := by
  intro xs
  induction xs with
  | nil => intro hxs; exact Bool.noConfusion hxs
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro hxs; exact Bool.noConfusion hxs
      | cons second rest =>
          intro hxs
          simp only [sortingReduceCells] at hxs
          rw [List.cons_append, List.cons_append]
          simp only [sortingReduceCells]
          by_cases hpair : slotValue second < slotValue first
          · rw [if_pos hpair]; rfl
          · rw [if_neg hpair] at hxs
            rw [if_neg hpair]
            rw [option_isSome_map] at hxs ⊢
            have spliced := ihTail hxs
            rw [List.cons_append] at spliced
            exact spliced

/-- Monotonicity under a left context: if the scanner fires on `ys`, it fires on `xs ++ ys`. -/
theorem sortingReduceCells_isSome_append_left {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) :
    ∀ (xs : List (OmegacECell dimension)) {ys : List (OmegacECell dimension)},
      (sortingReduceCells slotValue ys).isSome = true →
      (sortingReduceCells slotValue (xs ++ ys)).isSome = true := by
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
          simp only [sortingReduceCells]
          by_cases hpair : slotValue second < slotValue first
          · rw [if_pos hpair]; rfl
          · rw [if_neg hpair, option_isSome_map]
            rw [hzs] at tail
            exact tail

/-- Soundness: any reduct the scanner produces is reachable by a single sorting rewrite.  The head splice is a
`fire` of the guarded family member under a right context; the recursive descent is `underLeftContext`. -/
theorem sortingReduceCells_sound {dimension : Nat} (slotValue : OmegacECell dimension → Nat) :
    ∀ {xs ys : List (OmegacECell dimension)},
      sortingReduceCells slotValue xs = some ys →
      OmegacEWord.RewritesOneStep (sortingSystem slotValue) ⟨xs⟩ ⟨ys⟩ := by
  intro xs
  induction xs with
  | nil => intro ys hred; simp only [sortingReduceCells] at hred; nomatch hred
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro ys hred; simp only [sortingReduceCells] at hred; nomatch hred
      | cons second rest =>
          intro ys hred
          simp only [sortingReduceCells] at hred
          by_cases hpair : slotValue second < slotValue first
          · rw [if_pos hpair] at hred
            injection hred with hys
            subst hys
            exact OmegacEWord.RewritesOneStep.underRightContext ⟨rest⟩
              (sortingSwapRule_fires slotValue first second hpair)
          · rw [if_neg hpair] at hred
            cases hinner : sortingReduceCells slotValue (second :: rest) with
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

/-- Completeness core: whenever the system can step from `source`, the scanner fires on `source.cells`.  By
induction on the derivation — `fire` destructures the guarded existential membership and lands on the bare redex
(`sortingReduceCells_fires`); the context cases reuse the two monotonicity lemmas. -/
theorem sortingRewrite_implies_reduceCells_isSome {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (sortingSystem slotValue) source target →
      (sortingReduceCells slotValue source.cells).isSome = true := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      obtain ⟨biggerCell, smallerCell, descending, hrule⟩ := isInSystem
      subst hrule
      show (sortingReduceCells slotValue [biggerCell, smallerCell]).isSome = true
      rw [sortingReduceCells_fires slotValue biggerCell smallerCell descending]
      rfl
  | underLeftContext prefixWord _inner innerIH =>
      exact sortingReduceCells_isSome_append_left slotValue prefixWord.cells innerIH
  | underRightContext suffixWord _inner innerIH =>
      exact sortingReduceCells_isSome_append_right slotValue suffixWord.cells innerIH

/-- Word-level wrapper: lift the cell scanner to words. -/
def sortingReduceOnce {dimension : Nat} (slotValue : OmegacECell dimension → Nat)
    (word : OmegacEWord dimension) : Option (OmegacEWord dimension) :=
  (sortingReduceCells slotValue word.cells).map (fun reducedCells => { cells := reducedCells })

/-- The bundled reducer: leftmost descending-adjacency scanner with soundness + completeness (no distinctness). -/
def sortingWordReducer {dimension : Nat} (slotValue : OmegacECell dimension → Nat) :
    WordReducer (sortingSystem slotValue) where
  reduceOnce := sortingReduceOnce slotValue
  reduceOnce_sound := by
    intro word reduct hred
    simp only [sortingReduceOnce] at hred
    cases hcells : sortingReduceCells slotValue word.cells with
    | none =>
        rw [hcells] at hred
        simp only [Option.map_none] at hred
        nomatch hred
    | some ys =>
        rw [hcells] at hred
        simp only [Option.map_some] at hred
        injection hred with hreduct
        subst hreduct
        exact sortingReduceCells_sound slotValue hcells
  reduceOnce_complete := by
    intro word hnone reduct step
    have isSome := sortingRewrite_implies_reduceCells_isSome slotValue step
    simp only [sortingReduceOnce] at hnone
    cases hcells : sortingReduceCells slotValue word.cells with
    | none => rw [hcells] at isSome; exact Bool.noConfusion isSome
    | some ys =>
        rw [hcells] at hnone
        simp only [Option.map_some] at hnone
        nomatch hnone

/-- **SN-120 CAPSTONE (#623).**  The word problem for the sorting / symmetric-group (bubble-sort) system is
decidable.  Convergence = local confluence (`sortingHasLocalConfluence`, the braid critical pair) + termination
(`sortingSystem_isTerminating`, the inversion-count measure), fed through
`decidableConvertibleModulo_ofConvergent` with this bounded-search reducer.  NO distinctness hypothesis — the
strict-order guard is in the rule family's membership.  The third concrete fully-decided OmegacE presentation
(after SN-118 transposition and SN-119 absorption), and the genuine symmetric-group word-problem demonstration of
Leg-3 (Makkai/Forest). -/
def decidableConvertibleModulo_sortingSystem {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    (firstWord secondWord : OmegacEWord dimension) :
    Decidable (OmegacEWord.ConvertibleModulo (sortingSystem slotValue) firstWord secondWord) :=
  decidableConvertibleModulo_ofConvergent
    (sortingHasLocalConfluence slotValue)
    (sortingSystem_isTerminating slotValue)
    (sortingWordReducer slotValue) firstWord secondWord

end FX1Poly.OmegacE
