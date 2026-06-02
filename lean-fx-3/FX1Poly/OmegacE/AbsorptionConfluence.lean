import FX1Poly.OmegacE.AbsorptionSystem
import FX1Poly.OmegacE.IdempotentConfluence

/-! # FX1Poly/OmegacE/AbsorptionConfluence
    — structural inversion for the two-rule absorption system (SN-119 progress 2a, #622)

The decomposition layer for the absorption system's confluence: an absorption step IS "rewrite a mixed pair
to `[s,s]` in some context".  Because the system has TWO rules, the inversion carries a DISJUNCTION on the
source's redex shape — the genuinely new structure vs the single-rule transposition decomposition.

* `absorptionRewriteOneStep_decomposition` — forward inversion: a step `source ↦ target` means
  `target.cells = left ++ [s,s] ++ right` and `source.cells = left ++ [v,s] ++ right` OR
  `left ++ [s,v] ++ right` (which rule fired).  By induction on the rewrite; the `fire` case `rcases`-es the
  rule disjunction, the context cases reuse `listAppendAssoc` (the transposition-decomposition pattern).
* `absorptionRewriteOneStep_ofDecompositionLeft` / `…Right` — backward: rebuild a step from an explicit redex
  position, one per rule (`fire` under both contexts, re-associated by `listAppendAssoc`).

These are the critical-pair-extraction tools the local-confluence proof (next increment) consumes.  Generic
list-append helpers (`listAppendAssoc` …) are reused from `IdempotentConfluence`, as in `TranspositionConfluence`.

## Honest scope / deferred

This ships ONLY the decomposition layer.  The LOCAL CONFLUENCE proof is the next increment (SN-119 progress 2b):
the `listPrefixSplit` trichotomy on the two redex positions, with the genuine inter-rule critical pairs in the
one-cell-overlap case — `[v,s,v]` (reducts `[s,s,v]` / `[v,s,s]`, joining via one step EACH to `[s,s,s]`: the
genuinely-new multi-step join, NOT vacuous like transposition's overlap, NOT trivially-equal) and `[s,v,s]`
(both one-step reducts already `[s,s,s]`).  Same-position and disjoint cases are uniform (the disjoint
word-equalities mirror transposition's, since the reduct pair `[s,s]` is length-2 like `[b,a]`).  Then `newman`
+ the shipped `absorptionSystem_isTerminating` gives global confluence, and a two-rule `WordReducer` decides
the word problem (progress 3).

## Zero-axiom verification

All three lemmas verified `#print axioms`-clean in scratch before landing (the context cases are pure
`listAppendAssoc` `rw` chains; no `simp`, which leaks propext from its machinery).  Per-decl gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- **Structural inversion**: an absorption step IS "rewrite a mixed pair to `[s,s]` in context".  Target is
always `left ++ [s,s] ++ right`; source is `left ++ [v,s] ++ right` OR `left ++ [s,v] ++ right` — the
DISJUNCTION recording which of the two rules fired (the new structure vs the single-rule case). -/
theorem absorptionRewriteOneStep_decomposition {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell) source target →
      ∃ leftPart rightPart,
        target.cells = leftPart ++ [survivingCell, survivingCell] ++ rightPart ∧
        (source.cells = leftPart ++ [vanishingCell, survivingCell] ++ rightPart
          ∨ source.cells = leftPart ++ [survivingCell, vanishingCell] ++ rightPart) := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      rcases isInSystem with hLeft | hRight
      · subst hLeft; exact ⟨[], [], rfl, Or.inl rfl⟩
      · subst hRight; exact ⟨[], [], rfl, Or.inr rfl⟩
  | underLeftContext prefixWord _inner innerIH =>
      obtain ⟨leftPart, rightPart, hTgt, hSrc⟩ := innerIH
      refine ⟨prefixWord.cells ++ leftPart, rightPart, ?_, ?_⟩
      · show prefixWord.cells ++ _ = _
        rw [hTgt, ← listAppendAssoc, ← listAppendAssoc]
      · rcases hSrc with hSrcL | hSrcR
        · left
          show prefixWord.cells ++ _ = _
          rw [hSrcL, ← listAppendAssoc, ← listAppendAssoc]
        · right
          show prefixWord.cells ++ _ = _
          rw [hSrcR, ← listAppendAssoc, ← listAppendAssoc]
  | underRightContext suffixWord _inner innerIH =>
      obtain ⟨leftPart, rightPart, hTgt, hSrc⟩ := innerIH
      refine ⟨leftPart, rightPart ++ suffixWord.cells, ?_, ?_⟩
      · show _ ++ suffixWord.cells = _
        rw [hTgt, listAppendAssoc]
      · rcases hSrc with hSrcL | hSrcR
        · left
          show _ ++ suffixWord.cells = _
          rw [hSrcL, listAppendAssoc]
        · right
          show _ ++ suffixWord.cells = _
          rw [hSrcR, listAppendAssoc]

/-- **Backward (left rule)**: rebuild a left-rule step `[v,s] ↦ [s,s]` from an explicit redex position. -/
theorem absorptionRewriteOneStep_ofDecompositionLeft {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    (leftPart rightPart : List (OmegacECell dimension)) :
    OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      ⟨leftPart ++ [vanishingCell, survivingCell] ++ rightPart⟩
      ⟨leftPart ++ [survivingCell, survivingCell] ++ rightPart⟩ := by
  have fired : OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      ⟨leftPart ++ ([vanishingCell, survivingCell] ++ rightPart)⟩
      ⟨leftPart ++ ([survivingCell, survivingCell] ++ rightPart)⟩ :=
    OmegacEWord.RewritesOneStep.underLeftContext ⟨leftPart⟩
      (OmegacEWord.RewritesOneStep.underRightContext ⟨rightPart⟩
        (absorptionRuleVanishingLeft_fires vanishingCell survivingCell))
  rw [← listAppendAssoc, ← listAppendAssoc] at fired
  exact fired

/-- **Backward (right rule)**: rebuild a right-rule step `[s,v] ↦ [s,s]` from an explicit redex position. -/
theorem absorptionRewriteOneStep_ofDecompositionRight {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    (leftPart rightPart : List (OmegacECell dimension)) :
    OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      ⟨leftPart ++ [survivingCell, vanishingCell] ++ rightPart⟩
      ⟨leftPart ++ [survivingCell, survivingCell] ++ rightPart⟩ := by
  have fired : OmegacEWord.RewritesOneStep (absorptionSystem vanishingCell survivingCell)
      ⟨leftPart ++ ([survivingCell, vanishingCell] ++ rightPart)⟩
      ⟨leftPart ++ ([survivingCell, survivingCell] ++ rightPart)⟩ :=
    OmegacEWord.RewritesOneStep.underLeftContext ⟨leftPart⟩
      (OmegacEWord.RewritesOneStep.underRightContext ⟨rightPart⟩
        (absorptionRuleVanishingRight_fires vanishingCell survivingCell))
  rw [← listAppendAssoc, ← listAppendAssoc] at fired
  exact fired

end FX1Poly.OmegacE
