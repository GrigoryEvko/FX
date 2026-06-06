import FX1Poly.OmegacE.AbsorptionSystem
import FX1Poly.OmegacE.IdempotentConfluence

/-! # FX1Poly/OmegacE/AbsorptionConfluence
    — structural inversion for the two-rule absorption system

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

This ships ONLY the decomposition layer.  The LOCAL CONFLUENCE proof is the next increment:
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

/-- `[a,b,c] ++ rest = a :: b :: c :: rest` definitionally — the length-3 analogue of `doubleConsAppend`,
for the three-cell critical-pair words `[v,s,v]` / `[s,s,v]` / `[v,s,s]` / `[s,s,s]`. -/
theorem tripleConsAppend {alpha : Type _} (firstCell secondCell thirdCell : alpha)
    (rest : List alpha) :
    [firstCell, secondCell, thirdCell] ++ rest = firstCell :: secondCell :: thirdCell :: rest :=
  rfl

/-- **The genuine inter-rule critical pair join** (the mathematical heart of the absorption system).  The overlap word
`[v,s,v]` has two one-step reducts: `[s,s,v]` (rule-Left fired at the front `[v,s]`) and `[v,s,s]` (rule-Right
fired at the back `[s,v]`).  Both reduce in ONE further step to the common all-surviving word `[s,s,s]` —
`[s,s,v]` by firing rule-Right on its `[s,v]` suffix, `[v,s,s]` by firing rule-Left on its `[v,s]` prefix.

This is the join that is NOT vacuous (unlike transposition's one-cell overlap, which forced `a = b`) and NOT
trivially-equal (unlike the idempotent `[c,c,c]` overlap, whose reducts coincide).  It is the genuinely-new
multi-step critical-pair resolution that the absorption system contributes.  (The other overlap word `[s,v,s]` has both
one-step reducts already equal to `[s,s,s]`, so it joins by reflexivity — no lemma needed.) -/
theorem absorptionCriticalPairJoinLeftRight {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    (leftPart rightPart : List (OmegacECell dimension)) :
    OmegacEWord.Joinable (absorptionSystem vanishingCell survivingCell)
      ⟨leftPart ++ [survivingCell, survivingCell, vanishingCell] ++ rightPart⟩
      ⟨leftPart ++ [vanishingCell, survivingCell, survivingCell] ++ rightPart⟩ := by
  refine ⟨⟨leftPart ++ [survivingCell, survivingCell, survivingCell] ++ rightPart⟩, ?_, ?_⟩
  · have step := absorptionRewriteOneStep_ofDecompositionRight vanishingCell survivingCell
      (leftPart ++ [survivingCell]) rightPart
    have hsrc :
        (⟨leftPart ++ [survivingCell, survivingCell, vanishingCell] ++ rightPart⟩
          : OmegacEWord dimension)
        = ⟨(leftPart ++ [survivingCell]) ++ [survivingCell, vanishingCell] ++ rightPart⟩ := by
      apply congrArg OmegacEWord.mk
      rw [listAppendAssoc leftPart [survivingCell, survivingCell, vanishingCell] rightPart,
          listAppendAssoc (leftPart ++ [survivingCell]) [survivingCell, vanishingCell] rightPart,
          listAppendAssoc leftPart [survivingCell] ([survivingCell, vanishingCell] ++ rightPart),
          tripleConsAppend, singleConsAppend, doubleConsAppend]
    have htgt :
        (⟨(leftPart ++ [survivingCell]) ++ [survivingCell, survivingCell] ++ rightPart⟩
          : OmegacEWord dimension)
        = ⟨leftPart ++ [survivingCell, survivingCell, survivingCell] ++ rightPart⟩ := by
      apply congrArg OmegacEWord.mk
      rw [listAppendAssoc leftPart [survivingCell, survivingCell, survivingCell] rightPart,
          listAppendAssoc (leftPart ++ [survivingCell]) [survivingCell, survivingCell] rightPart,
          listAppendAssoc leftPart [survivingCell] ([survivingCell, survivingCell] ++ rightPart),
          tripleConsAppend, singleConsAppend, doubleConsAppend]
    rw [hsrc, ← htgt]
    exact OmegacEWord.RewritesMany.single step
  · have step := absorptionRewriteOneStep_ofDecompositionLeft vanishingCell survivingCell
      leftPart ([survivingCell] ++ rightPart)
    have hsrc :
        (⟨leftPart ++ [vanishingCell, survivingCell, survivingCell] ++ rightPart⟩
          : OmegacEWord dimension)
        = ⟨leftPart ++ [vanishingCell, survivingCell] ++ ([survivingCell] ++ rightPart)⟩ := by
      apply congrArg OmegacEWord.mk
      rw [listAppendAssoc leftPart [vanishingCell, survivingCell, survivingCell] rightPart,
          listAppendAssoc leftPart [vanishingCell, survivingCell] ([survivingCell] ++ rightPart),
          tripleConsAppend, doubleConsAppend, singleConsAppend]
    have htgt :
        (⟨leftPart ++ [survivingCell, survivingCell] ++ ([survivingCell] ++ rightPart)⟩
          : OmegacEWord dimension)
        = ⟨leftPart ++ [survivingCell, survivingCell, survivingCell] ++ rightPart⟩ := by
      apply congrArg OmegacEWord.mk
      rw [listAppendAssoc leftPart [survivingCell, survivingCell, survivingCell] rightPart,
          listAppendAssoc leftPart [survivingCell, survivingCell] ([survivingCell] ++ rightPart),
          tripleConsAppend, doubleConsAppend, singleConsAppend]
    rw [hsrc, ← htgt]
    exact OmegacEWord.RewritesMany.single step

/-- **Disjoint redexes commute** — the third trichotomy branch of local confluence (the bulk).  Two
non-overlapping redexes separated by `mid'`: firing the left one (`pairA → [s,s]`) and the right one
(`pairB → [s,s]`) both reach the common all-`[s,s]` word.  The crucial economy: the word equalities are PURE
associativity (the pairs stay opaque as `++ pairA` / `++ pairB`, never cons-collapsed), so this SINGLE helper
covers all four rule combinations — the rule disjunction is consumed only at the two `_ofDecomposition` fires.
This is exactly the transposition disjoint-commute case generalized to two distinct rules with no extra case-blowup. -/
theorem absorptionJoinableDisjoint {dimension : Nat}
    (vanishingCell survivingCell : OmegacECell dimension)
    (leftA mid' rightB pairA pairB : List (OmegacECell dimension))
    (hPairA : pairA = [vanishingCell, survivingCell] ∨ pairA = [survivingCell, vanishingCell])
    (hPairB : pairB = [vanishingCell, survivingCell] ∨ pairB = [survivingCell, vanishingCell]) :
    OmegacEWord.Joinable (absorptionSystem vanishingCell survivingCell)
      ⟨leftA ++ [survivingCell, survivingCell] ++ (mid' ++ pairB ++ rightB)⟩
      ⟨(leftA ++ pairA ++ mid') ++ [survivingCell, survivingCell] ++ rightB⟩ := by
  refine ⟨⟨leftA ++ [survivingCell, survivingCell] ++ mid'
            ++ [survivingCell, survivingCell] ++ rightB⟩, ?_, ?_⟩
  · have hsrc :
        (⟨leftA ++ [survivingCell, survivingCell] ++ (mid' ++ pairB ++ rightB)⟩
          : OmegacEWord dimension)
        = ⟨(leftA ++ [survivingCell, survivingCell] ++ mid') ++ pairB ++ rightB⟩ := by
      apply congrArg OmegacEWord.mk
      rw [← listAppendAssoc (leftA ++ [survivingCell, survivingCell]) (mid' ++ pairB) rightB,
          ← listAppendAssoc (leftA ++ [survivingCell, survivingCell]) mid' pairB]
    rw [hsrc]
    rcases hPairB with hB | hB
    · subst hB
      exact OmegacEWord.RewritesMany.single
        (absorptionRewriteOneStep_ofDecompositionLeft vanishingCell survivingCell
          (leftA ++ [survivingCell, survivingCell] ++ mid') rightB)
    · subst hB
      exact OmegacEWord.RewritesMany.single
        (absorptionRewriteOneStep_ofDecompositionRight vanishingCell survivingCell
          (leftA ++ [survivingCell, survivingCell] ++ mid') rightB)
  · have hsrc :
        (⟨(leftA ++ pairA ++ mid') ++ [survivingCell, survivingCell] ++ rightB⟩
          : OmegacEWord dimension)
        = ⟨leftA ++ pairA ++ (mid' ++ [survivingCell, survivingCell] ++ rightB)⟩ := by
      apply congrArg OmegacEWord.mk
      rw [listAppendAssoc (leftA ++ pairA ++ mid') [survivingCell, survivingCell] rightB,
          listAppendAssoc (leftA ++ pairA) mid' ([survivingCell, survivingCell] ++ rightB),
          ← listAppendAssoc mid' [survivingCell, survivingCell] rightB]
    have htgt :
        (⟨leftA ++ [survivingCell, survivingCell] ++ (mid' ++ [survivingCell, survivingCell] ++ rightB)⟩
          : OmegacEWord dimension)
        = ⟨leftA ++ [survivingCell, survivingCell] ++ mid'
            ++ [survivingCell, survivingCell] ++ rightB⟩ := by
      apply congrArg OmegacEWord.mk
      rw [← listAppendAssoc (leftA ++ [survivingCell, survivingCell])
            (mid' ++ [survivingCell, survivingCell]) rightB,
          ← listAppendAssoc (leftA ++ [survivingCell, survivingCell]) mid'
            [survivingCell, survivingCell]]
    rw [hsrc, ← htgt]
    rcases hPairA with hA | hA
    · subst hA
      exact OmegacEWord.RewritesMany.single
        (absorptionRewriteOneStep_ofDecompositionLeft vanishingCell survivingCell
          leftA (mid' ++ [survivingCell, survivingCell] ++ rightB))
    · subst hA
      exact OmegacEWord.RewritesMany.single
        (absorptionRewriteOneStep_ofDecompositionRight vanishingCell survivingCell
          leftA (mid' ++ [survivingCell, survivingCell] ++ rightB))

end FX1Poly.OmegacE
