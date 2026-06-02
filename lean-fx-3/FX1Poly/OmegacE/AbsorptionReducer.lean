import FX1Poly.OmegacE.AbsorptionLocalConfluence
import FX1Poly.OmegacE.IdempotentReducer

/-! # FX1Poly/OmegacE/AbsorptionReducer
    — the SN-119 CAPSTONE (#622): decidable word problem for the two-rule absorption system

The final atom that CLOSES SN-119.  A bounded-search `WordReducer` for the two-rule absorption system, fed
through `decidableConvertibleModulo_ofConvergent` with the shipped convergence
(`absorptionHasLocalConfluence` + `absorptionSystem_isTerminating`).

* `absorptionReduceCells` — leftmost-redex scanner.  Both rules splice a mixed adjacent pair to `[s,s]`, so a
  SINGLE combined condition `(first=v ∧ second=s) ∨ (first=s ∧ second=v)` covers both — the genuinely-two-rule
  structure handled by ONE `if`.  `none` exactly when no mixed adjacency exists.
* `absorptionReduceCells_firesLeft` / `…firesRight` — the scanner fires on each bare redex (`Or.inl`/`Or.inr`
  witness; NO distinctness needed, since BOTH branches splice to `[s,s]`).
* monotonicity (`…isSome_append_right/left`, reusing the generic `option_isSome_map`) + soundness
  (`…sound`, the fire case `rcases`-es the disjunction CONDITION to pick rule-Left/Right) + completeness
  (`absorptionRewrite_implies_reduceCells_isSome`, the fire case `rcases`-es the rule DISJUNCTION).
* `absorptionWordReducer` — the bundle (NO distinctness needed; sound + complete hold even at `v=s`).
* `decidableConvertibleModulo_absorptionSystem` — **the SN-119 capstone**: the word problem for the two-rule
  absorption system is decidable.  Distinctness `v ≠ s` is what the convergence (termination) needs.  This makes
  the absorption system the FIRST FULLY-DECIDED two-rule presentation with genuine inter-rule critical pairs —
  SN-119 complete.

## Zero-axiom verification

All declarations verified `#print axioms`-clean in scratch before landing (faithful mirror of the gated
`TranspositionReducer`, with the two-rule disjunction-`if`).  Per-decl gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- Leftmost-redex scanner for the two-rule absorption system.  Both rules splice a mixed adjacent pair to
`[s,s]`, so a single combined condition `(first=v ∧ second=s) ∨ (first=s ∧ second=v)` covers both. -/
def absorptionReduceCells {dimension : Nat} (vanishingCell survivingCell : OmegacECell dimension) :
    List (OmegacECell dimension) → Option (List (OmegacECell dimension))
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if (first = vanishingCell ∧ second = survivingCell)
          ∨ (first = survivingCell ∧ second = vanishingCell) then
        some (survivingCell :: survivingCell :: rest)
      else
        (absorptionReduceCells vanishingCell survivingCell (second :: rest)).map
          (fun reducedTail => first :: reducedTail)

theorem absorptionReduceCells_firesLeft {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    absorptionReduceCells vanishingCell survivingCell [vanishingCell, survivingCell]
      = some [survivingCell, survivingCell] := by
  dsimp only [absorptionReduceCells]
  rw [if_pos (Or.inl (And.intro rfl rfl))]

theorem absorptionReduceCells_firesRight {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    absorptionReduceCells vanishingCell survivingCell [survivingCell, vanishingCell]
      = some [survivingCell, survivingCell] := by
  dsimp only [absorptionReduceCells]
  rw [if_pos (Or.inr (And.intro rfl rfl))]

theorem absorptionReduceCells_isSome_append_right {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) (ys : List (OmegacECell dimension)) :
    ∀ {xs : List (OmegacECell dimension)},
      (absorptionReduceCells vanishingCell survivingCell xs).isSome = true →
      (absorptionReduceCells vanishingCell survivingCell (xs ++ ys)).isSome = true := by
  intro xs
  induction xs with
  | nil => intro hxs; exact Bool.noConfusion hxs
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro hxs; exact Bool.noConfusion hxs
      | cons second rest =>
          intro hxs
          simp only [absorptionReduceCells] at hxs
          rw [List.cons_append, List.cons_append]
          simp only [absorptionReduceCells]
          by_cases hcond : (first = vanishingCell ∧ second = survivingCell)
              ∨ (first = survivingCell ∧ second = vanishingCell)
          · rw [if_pos hcond]; rfl
          · rw [if_neg hcond] at hxs
            rw [if_neg hcond]
            rw [option_isSome_map] at hxs ⊢
            have spliced := ihTail hxs
            rw [List.cons_append] at spliced
            exact spliced

theorem absorptionReduceCells_isSome_append_left {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    ∀ (xs : List (OmegacECell dimension)) {ys : List (OmegacECell dimension)},
      (absorptionReduceCells vanishingCell survivingCell ys).isSome = true →
      (absorptionReduceCells vanishingCell survivingCell (xs ++ ys)).isSome = true := by
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
          simp only [absorptionReduceCells]
          by_cases hcond : (first = vanishingCell ∧ second = survivingCell)
              ∨ (first = survivingCell ∧ second = vanishingCell)
          · rw [if_pos hcond]; rfl
          · rw [if_neg hcond, option_isSome_map]
            rw [hzs] at tail
            exact tail

theorem absorptionReduceCells_sound {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    ∀ {xs ys : List (OmegacECell dimension)},
      absorptionReduceCells vanishingCell survivingCell xs = some ys →
      OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell) ⟨xs⟩ ⟨ys⟩ := by
  intro xs
  induction xs with
  | nil => intro ys hred; simp only [absorptionReduceCells] at hred; nomatch hred
  | cons first xs' ihTail =>
      cases xs' with
      | nil => intro ys hred; simp only [absorptionReduceCells] at hred; nomatch hred
      | cons second rest =>
          intro ys hred
          simp only [absorptionReduceCells] at hred
          by_cases hcond : (first = vanishingCell ∧ second = survivingCell)
              ∨ (first = survivingCell ∧ second = vanishingCell)
          · rw [if_pos hcond] at hred
            injection hred with hys
            subst hys
            rcases hcond with ⟨hFirst, hSecond⟩ | ⟨hFirst, hSecond⟩
            · rw [hFirst, hSecond]
              exact OmegacEWord.RewritesOneStep.underRightContext ⟨rest⟩
                (absorptionRuleVanishingLeft_fires vanishingCell survivingCell)
            · rw [hFirst, hSecond]
              exact OmegacEWord.RewritesOneStep.underRightContext ⟨rest⟩
                (absorptionRuleVanishingRight_fires vanishingCell survivingCell)
          · rw [if_neg hcond] at hred
            cases hinner : absorptionReduceCells vanishingCell survivingCell (second :: rest) with
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

theorem absorptionRewrite_implies_reduceCells_isSome {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell) source target →
      (absorptionReduceCells vanishingCell survivingCell source.cells).isSome = true := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      rcases isInSystem with hLeft | hRight
      · subst hLeft
        show (absorptionReduceCells vanishingCell survivingCell
          [vanishingCell, survivingCell]).isSome = true
        rw [absorptionReduceCells_firesLeft]; rfl
      · subst hRight
        show (absorptionReduceCells vanishingCell survivingCell
          [survivingCell, vanishingCell]).isSome = true
        rw [absorptionReduceCells_firesRight]; rfl
  | underLeftContext prefixWord _inner innerIH =>
      exact absorptionReduceCells_isSome_append_left vanishingCell survivingCell prefixWord.cells innerIH
  | underRightContext suffixWord _inner innerIH =>
      exact absorptionReduceCells_isSome_append_right vanishingCell survivingCell suffixWord.cells innerIH

def absorptionReduceOnce {dimension : Nat} (vanishingCell survivingCell : OmegacECell dimension)
    (word : OmegacEWord dimension) : Option (OmegacEWord dimension) :=
  (absorptionReduceCells vanishingCell survivingCell word.cells).map (fun reducedCells => { cells := reducedCells })

def absorptionWordReducer {dimension : Nat} (vanishingCell survivingCell : OmegacECell dimension) :
    WordReducer (absorptionSystem vanishingCell survivingCell) where
  reduceOnce := absorptionReduceOnce vanishingCell survivingCell
  reduceOnce_sound := by
    intro word reduct hred
    simp only [absorptionReduceOnce] at hred
    cases hcells : absorptionReduceCells vanishingCell survivingCell word.cells with
    | none =>
        rw [hcells] at hred
        simp only [Option.map_none] at hred
        nomatch hred
    | some ys =>
        rw [hcells] at hred
        simp only [Option.map_some] at hred
        injection hred with hreduct
        subst hreduct
        exact absorptionReduceCells_sound vanishingCell survivingCell hcells
  reduceOnce_complete := by
    intro word hnone reduct step
    have isSome := absorptionRewrite_implies_reduceCells_isSome vanishingCell survivingCell step
    simp only [absorptionReduceOnce] at hnone
    cases hcells : absorptionReduceCells vanishingCell survivingCell word.cells with
    | none => rw [hcells] at isSome; exact Bool.noConfusion isSome
    | some ys =>
        rw [hcells] at hnone
        simp only [Option.map_some] at hnone
        nomatch hnone

def decidableConvertibleModulo_absorptionSystem {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) (distinct : vanishingCell ≠ survivingCell)
    (firstWord secondWord : OmegacEWord dimension) :
    Decidable (OmegacEWord.ConvertibleModulo (absorptionSystem vanishingCell survivingCell)
      firstWord secondWord) :=
  decidableConvertibleModulo_ofConvergent
    (absorptionHasLocalConfluence vanishingCell survivingCell distinct)
    (absorptionSystem_isTerminating vanishingCell survivingCell distinct)
    (absorptionWordReducer vanishingCell survivingCell) firstWord secondWord

end FX1Poly.OmegacE
