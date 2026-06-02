import FX1Poly.OmegacE.SortingTermination
import FX1Poly.OmegacE.IdempotentConfluence

/-! # FX1Poly/OmegacE/SortingConfluence
    — the sorting/symmetric system's structural inversion + the BRAID critical-pair join (SN-120 progress 3, #623)

`SortingTermination.lean` shipped the guarded sorting system (`[a,b] → [b,a]` when `slotValue b < slotValue a`),
its length invariants, and its TERMINATION (inversion-count measure).  This file builds toward CONFLUENCE.

The sorting system is the "graduation" of the OmegacE convergent-system sequence (SN-118 transposition, SN-119
absorption): its one-cell overlap is the genuine **braid critical pair**, NOT a vacuous/degenerate case.  Where
transposition's single-cell overlap forced `a = b` (impossible, `absurd`) and absorption's joined in a single step,
the sorting system's overlap is a strictly descending triple `[a,b,c]` (`slotValue c < slotValue b < slotValue a`)
whose two reducts join via genuinely MULTI-step sequences — the braid relation `aba = bab` of the symmetric group.

* `sortingRewriteOneStep_decomposition` / `…_ofDecomposition` — structural inversion: a one-step sorting rewrite
  is exactly `A ++ [a,b] ++ B ↦ A ++ [b,a] ++ B` with the guard `slotValue b < slotValue a` (and conversely).
  Unlike the transposition twin, the cells `a`, `b` and the guard are EXISTENTIALLY produced (the rule is a
  guarded family, `∃ a b, slotValue b < slotValue a ∧ rule = sortingSwapRule a b`, not a fixed pair).
* `sortingBraidCriticalPairJoinBare` — THE braid join: for `slotValue c < slotValue b < slotValue a`, the front
  reduct `[b,a,c]` and the back reduct `[a,c,b]` of `[a,b,c]` both reach the sorted `[c,b,a]` in two steps each
  (`[b,a,c] → [b,c,a] → [c,b,a]` and `[a,c,b] → [c,a,b] → [c,b,a]`).  Every intermediate redex's guard is one of
  `hba`/`hcb`/`hca` (the last by `Nat.lt_trans`); the concrete-list appends in `ofDecomposition` compute by defeq,
  so the bare layer needs no word-equality massaging.

## Honest scope / deferred

This ships the decomposition + the bare braid critical-pair join.  The remaining SN-120 confluence atoms:
the CONTEXT lift of the braid join (`A ++ [a,b,c] ++ B`), the disjoint-commute case (two non-overlapping redexes
commute — structurally identical to the transposition/absorption disjoint case, reduct `[b,a]` length-2), then
`sortingJoinableWhenLeftShorter` (prefix-split trichotomy: nil = equal reducts / single = braid critical pair /
cons-cons = disjoint) → `sortingHasLocalConfluence` → `sortingHasConfluence` (`newman` + the shipped
`sortingSystem_isTerminating`).  Finally the guarded `WordReducer` + `decidableConvertibleModulo_ofConvergent`
close SN-120.

## Zero-axiom verification

The decomposition mirrors `transpositionRewriteOneStep_decomposition` (existential rule instead of a fixed pair);
the braid join builds four `ofDecomposition` steps whose endpoints are defeq to the concrete triples (so the four
`RewritesOneStep`s typecheck directly, composed by `RewritesMany.step`/`.single`).  Generic word-list helpers
(`listAppendAssoc`) are reused from `IdempotentConfluence`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- **Structural inversion**: any one-step sorting rewrite is `A ++ [a,b] ++ B ↦ A ++ [b,a] ++ B` with the strict
guard `slotValue b < slotValue a`, for some context `A`, `B`.  By induction on the derivation: the `fire` case
destructures the guarded existential membership (`∃ a b, slotValue b < slotValue a ∧ rule = sortingSwapRule a b`)
to produce the cells + guard with empty context; the context cases extend the left/right part via
`listAppendAssoc`. -/
theorem sortingRewriteOneStep_decomposition {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (sortingSystem slotValue) source target →
      ∃ leftPart rightPart biggerCell smallerCell,
        slotValue smallerCell < slotValue biggerCell ∧
        source.cells = leftPart ++ [biggerCell, smallerCell] ++ rightPart ∧
        target.cells = leftPart ++ [smallerCell, biggerCell] ++ rightPart := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      obtain ⟨biggerCell, smallerCell, descending, hrule⟩ := isInSystem
      subst hrule
      exact ⟨[], [], biggerCell, smallerCell, descending, rfl, rfl⟩
  | underLeftContext prefixWord _inner innerIH =>
      obtain ⟨leftPart, rightPart, biggerCell, smallerCell, descending, hSrc, hTgt⟩ := innerIH
      refine ⟨prefixWord.cells ++ leftPart, rightPart, biggerCell, smallerCell, descending, ?_, ?_⟩
      · show prefixWord.cells ++ _ = _
        rw [hSrc, ← listAppendAssoc, ← listAppendAssoc]
      · show prefixWord.cells ++ _ = _
        rw [hTgt, ← listAppendAssoc, ← listAppendAssoc]
  | underRightContext suffixWord _inner innerIH =>
      obtain ⟨leftPart, rightPart, biggerCell, smallerCell, descending, hSrc, hTgt⟩ := innerIH
      refine ⟨leftPart, rightPart ++ suffixWord.cells, biggerCell, smallerCell, descending, ?_, ?_⟩
      · show _ ++ suffixWord.cells = _
        rw [hSrc, listAppendAssoc]
      · show _ ++ suffixWord.cells = _
        rw [hTgt, listAppendAssoc]

/-- **Backward characterization**: any `A ++ [a,b] ++ B → A ++ [b,a] ++ B` with `slotValue b < slotValue a` IS a
one-step sorting rewrite (`fire` of the guarded family member under the right then left context). -/
theorem sortingRewriteOneStep_ofDecomposition {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    (leftPart rightPart : List (OmegacECell dimension))
    (biggerCell smallerCell : OmegacECell dimension)
    (descending : slotValue smallerCell < slotValue biggerCell) :
    OmegacEWord.RewritesOneStep (sortingSystem slotValue)
      ⟨leftPart ++ [biggerCell, smallerCell] ++ rightPart⟩
      ⟨leftPart ++ [smallerCell, biggerCell] ++ rightPart⟩ := by
  have fired : OmegacEWord.RewritesOneStep (sortingSystem slotValue)
      ⟨leftPart ++ ([biggerCell, smallerCell] ++ rightPart)⟩
      ⟨leftPart ++ ([smallerCell, biggerCell] ++ rightPart)⟩ :=
    OmegacEWord.RewritesOneStep.underLeftContext ⟨leftPart⟩
      (OmegacEWord.RewritesOneStep.underRightContext ⟨rightPart⟩
        (sortingSwapRule_fires slotValue biggerCell smallerCell descending))
  rw [← listAppendAssoc, ← listAppendAssoc] at fired
  exact fired

/-- **The braid critical-pair join (bare triple)** — the heart of SN-120.  For a strictly descending triple
`slotValue c < slotValue b < slotValue a`, the two one-step reducts of `[a,b,c]` — the front swap `[b,a,c]` and
the back swap `[a,c,b]` — both reduce in TWO steps to the fully sorted `[c,b,a]`.  This is the braid relation
`aba = bab` of the symmetric group, and the first genuine MULTI-step `RewritesMany` join in the OmegacE sequence
(vs the single-step joins of absorption).  Every intermediate redex's guard is one of `hba`/`hcb`/`hca` (the last
by `Nat.lt_trans`); the concrete-list appends in `ofDecomposition` compute by defeq, so the four `ofDecomposition`
steps typecheck directly against the concrete triples without word massaging. -/
theorem sortingBraidCriticalPairJoinBare {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    (cellA cellB cellC : OmegacECell dimension)
    (hba : slotValue cellB < slotValue cellA)
    (hcb : slotValue cellC < slotValue cellB) :
    OmegacEWord.Joinable (sortingSystem slotValue)
      ⟨[cellB, cellA, cellC]⟩
      ⟨[cellA, cellC, cellB]⟩ := by
  have hca : slotValue cellC < slotValue cellA := Nat.lt_trans hcb hba
  -- Front reduct: [b,a,c] → [b,c,a] → [c,b,a].
  have stepFrontA : OmegacEWord.RewritesOneStep (sortingSystem slotValue)
      ⟨[cellB, cellA, cellC]⟩ ⟨[cellB, cellC, cellA]⟩ :=
    sortingRewriteOneStep_ofDecomposition slotValue [cellB] [] cellA cellC hca
  have stepFrontB : OmegacEWord.RewritesOneStep (sortingSystem slotValue)
      ⟨[cellB, cellC, cellA]⟩ ⟨[cellC, cellB, cellA]⟩ :=
    sortingRewriteOneStep_ofDecomposition slotValue [] [cellA] cellB cellC hcb
  -- Back reduct: [a,c,b] → [c,a,b] → [c,b,a].
  have stepBackA : OmegacEWord.RewritesOneStep (sortingSystem slotValue)
      ⟨[cellA, cellC, cellB]⟩ ⟨[cellC, cellA, cellB]⟩ :=
    sortingRewriteOneStep_ofDecomposition slotValue [] [cellB] cellA cellC hca
  have stepBackB : OmegacEWord.RewritesOneStep (sortingSystem slotValue)
      ⟨[cellC, cellA, cellB]⟩ ⟨[cellC, cellB, cellA]⟩ :=
    sortingRewriteOneStep_ofDecomposition slotValue [cellC] [] cellA cellB hba
  exact ⟨⟨[cellC, cellB, cellA]⟩,
    OmegacEWord.RewritesMany.step stepFrontA (OmegacEWord.RewritesMany.single stepFrontB),
    OmegacEWord.RewritesMany.step stepBackA (OmegacEWord.RewritesMany.single stepBackB)⟩

/-- **Lift a bare joinability into a surrounding context** `leftCtx _ rightCtx`.  Generic (any system): both
reduction sequences are wrapped by `RewritesMany.underRightContext`/`underLeftContext`, and the source words are
reassociated `(leftCtx ++ bare) ++ rightCtx = leftCtx ++ (bare ++ rightCtx)` (the only step that is not defeq,
since `OmegacEWord.append` IS `++` on cells) to match the lifted form.  The common reduct is taken in the lifted
(right-associated) shape so both legs land on it directly. -/
theorem OmegacEWord.Joinable.inContext {dimension : Nat}
    {system : OmegacERewriteRule dimension → Prop}
    (leftCtx rightCtx : List (OmegacECell dimension))
    {bareLeft bareRight : List (OmegacECell dimension)}
    (joinable : OmegacEWord.Joinable system ⟨bareLeft⟩ ⟨bareRight⟩) :
    OmegacEWord.Joinable system
      ⟨leftCtx ++ bareLeft ++ rightCtx⟩ ⟨leftCtx ++ bareRight ++ rightCtx⟩ := by
  obtain ⟨⟨commonCells⟩, manyLeft, manyRight⟩ := joinable
  refine ⟨⟨leftCtx ++ (commonCells ++ rightCtx)⟩, ?_, ?_⟩
  · rw [show (⟨leftCtx ++ bareLeft ++ rightCtx⟩ : OmegacEWord dimension)
        = ⟨leftCtx ++ (bareLeft ++ rightCtx)⟩ from
        congrArg OmegacEWord.mk (listAppendAssoc leftCtx bareLeft rightCtx)]
    exact (manyLeft.underRightContext ⟨rightCtx⟩).underLeftContext ⟨leftCtx⟩
  · rw [show (⟨leftCtx ++ bareRight ++ rightCtx⟩ : OmegacEWord dimension)
        = ⟨leftCtx ++ (bareRight ++ rightCtx)⟩ from
        congrArg OmegacEWord.mk (listAppendAssoc leftCtx bareRight rightCtx)]
    exact (manyRight.underRightContext ⟨rightCtx⟩).underLeftContext ⟨leftCtx⟩

/-- **The braid critical-pair join in context** — `sortingBraidCriticalPairJoinBare` lifted under an arbitrary
surrounding context, ready for the one-cell-overlap case of local confluence.  In `sortingJoinableWhenLeftShorter`
the single-cell overlap `[a,b,c]` produces exactly `⟨leftA ++ [b,a,c] ++ rightB⟩` / `⟨leftA ++ [a,c,b] ++ rightB⟩`,
which this lemma joins directly (the new content of SN-120, vs the vacuous/absurd one-cell case of transposition). -/
theorem sortingBraidCriticalPairJoin {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    (leftCtx rightCtx : List (OmegacECell dimension))
    (cellA cellB cellC : OmegacECell dimension)
    (hba : slotValue cellB < slotValue cellA)
    (hcb : slotValue cellC < slotValue cellB) :
    OmegacEWord.Joinable (sortingSystem slotValue)
      ⟨leftCtx ++ [cellB, cellA, cellC] ++ rightCtx⟩
      ⟨leftCtx ++ [cellA, cellC, cellB] ++ rightCtx⟩ :=
  (sortingBraidCriticalPairJoinBare slotValue cellA cellB cellC hba hcb).inContext leftCtx rightCtx

/-- **When the left redex is the shorter prefix, the two reducts are joinable.**  Prefix-split the shared source,
then case on the overlap `mid`:
* `[]` (same position) — injection gives `biggerA = biggerB`, `smallerA = smallerB`, `rightA = rightB`, so the two
  reducts are EQUAL (joined trivially via `joinable_of_wordEq`).  Unlike transposition this is never a mismatch.
* `[m]` (one-cell overlap) — THE BRAID critical pair: injection gives `biggerA = m`, `smallerA = biggerB`,
  `rightA = smallerB :: rightB`, so the reducts are `⟨leftA ++ [smallerA,biggerA,smallerB] ++ rightB⟩` /
  `⟨leftA ++ [biggerA,smallerB,smallerA] ++ rightB⟩`, joined by `sortingBraidCriticalPairJoin` (guard `hcb` from
  `hB` via `smallerA = biggerB`).  This is the genuinely-new content vs transposition's vacuous one-cell case.
* `m :: m2 :: mid'` (disjoint) — the redexes commute: each reduct fires the other still-present redex, meeting at
  the doubly-reduced word (structurally identical to the transposition/absorption disjoint case). -/
theorem sortingJoinableWhenLeftShorter {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    (leftA rightA leftB rightB : List (OmegacECell dimension))
    (biggerA smallerA biggerB smallerB : OmegacECell dimension)
    (hA : slotValue smallerA < slotValue biggerA)
    (hB : slotValue smallerB < slotValue biggerB)
    (hEq : leftA ++ [biggerA, smallerA] ++ rightA = leftB ++ [biggerB, smallerB] ++ rightB)
    (hLen : leftA.length ≤ leftB.length) :
    OmegacEWord.Joinable (sortingSystem slotValue)
      ⟨leftA ++ [smallerA, biggerA] ++ rightA⟩
      ⟨leftB ++ [smallerB, biggerB] ++ rightB⟩ := by
  rw [listAppendAssoc, listAppendAssoc] at hEq
  obtain ⟨mid, hMid, hRest⟩ :=
    listPrefixSplit leftA leftB ([biggerA, smallerA] ++ rightA)
      ([biggerB, smallerB] ++ rightB) hEq hLen
  rw [doubleConsAppend, doubleConsAppend] at hRest
  cases mid with
  | nil =>
      rw [List.nil_append] at hRest
      injection hRest with hBig hRest1
      injection hRest1 with hSml hRights
      subst hBig
      subst hSml
      subst hRights
      subst hMid
      apply joinable_of_wordEq
      apply congrArg OmegacEWord.mk
      rw [listAppendNil]
  | cons m midTail =>
      cases midTail with
      | nil =>
          rw [List.cons_append, List.nil_append] at hRest
          injection hRest with hm hRest1
          injection hRest1 with hSmlEqBigB hRights
          subst hm
          subst hRights
          subst hMid
          have hcb : slotValue smallerB < slotValue smallerA := by
            rw [hSmlEqBigB]; exact hB
          have braid := sortingBraidCriticalPairJoin slotValue leftA rightB biggerA smallerA smallerB hA hcb
          have hFirst : (⟨leftA ++ [smallerA, biggerA] ++ (smallerB :: rightB)⟩ : OmegacEWord dimension)
              = ⟨leftA ++ [smallerA, biggerA, smallerB] ++ rightB⟩ := by
            apply congrArg OmegacEWord.mk
            rw [listAppendAssoc leftA [smallerA, biggerA] (smallerB :: rightB),
                listAppendAssoc leftA [smallerA, biggerA, smallerB] rightB]
            rfl
          have hSecond : (⟨leftA ++ [biggerA] ++ [smallerB, biggerB] ++ rightB⟩ : OmegacEWord dimension)
              = ⟨leftA ++ [biggerA, smallerB, smallerA] ++ rightB⟩ := by
            apply congrArg OmegacEWord.mk
            rw [hSmlEqBigB, listAppendAssoc (leftA ++ [biggerA]) [smallerB, biggerB] rightB,
                listAppendAssoc leftA [biggerA] ([smallerB, biggerB] ++ rightB),
                listAppendAssoc leftA [biggerA, smallerB, biggerB] rightB]
            rfl
          rw [hFirst, hSecond]
          exact braid
      | cons m2 mid' =>
          rw [List.cons_append, List.cons_append] at hRest
          injection hRest with hm1 hRest1
          injection hRest1 with hm2 hRights
          subst hm1
          subst hm2
          subst hRights
          subst hMid
          refine ⟨⟨leftA ++ [smallerA, biggerA] ++ mid' ++ [smallerB, biggerB] ++ rightB⟩, ?_, ?_⟩
          · have step := sortingRewriteOneStep_ofDecomposition slotValue
              (leftA ++ [smallerA, biggerA] ++ mid') rightB biggerB smallerB hB
            have hsrc :
                (⟨leftA ++ [smallerA, biggerA] ++ (mid' ++ (biggerB :: smallerB :: rightB))⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [smallerA, biggerA] ++ mid' ++ [biggerB, smallerB] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc (leftA ++ [smallerA, biggerA] ++ mid') [biggerB, smallerB] rightB,
                  doubleConsAppend,
                  listAppendAssoc (leftA ++ [smallerA, biggerA]) mid'
                    (biggerB :: smallerB :: rightB)]
            rw [hsrc]
            exact OmegacEWord.RewritesMany.single step
          · have step := sortingRewriteOneStep_ofDecomposition slotValue
              leftA (mid' ++ [smallerB, biggerB] ++ rightB) biggerA smallerA hA
            have hsrc :
                (⟨leftA ++ biggerA :: smallerA :: mid' ++ [smallerB, biggerB] ++ rightB⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [biggerA, smallerA] ++ (mid' ++ [smallerB, biggerB] ++ rightB)⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc leftA [biggerA, smallerA]
                    (mid' ++ [smallerB, biggerB] ++ rightB),
                  doubleConsAppend biggerA smallerA
                    (mid' ++ [smallerB, biggerB] ++ rightB),
                  listAppendAssoc (leftA ++ (biggerA :: smallerA :: mid')) [smallerB, biggerB]
                    rightB,
                  listAppendAssoc leftA (biggerA :: smallerA :: mid')
                    ([smallerB, biggerB] ++ rightB),
                  List.cons_append, List.cons_append,
                  listAppendAssoc mid' [smallerB, biggerB] rightB]
            have htgt :
                (⟨leftA ++ [smallerA, biggerA] ++ (mid' ++ [smallerB, biggerB] ++ rightB)⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [smallerA, biggerA] ++ mid' ++ [smallerB, biggerB] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc ((leftA ++ [smallerA, biggerA]) ++ mid') [smallerB, biggerB]
                    rightB,
                  listAppendAssoc (leftA ++ [smallerA, biggerA]) mid'
                    ([smallerB, biggerB] ++ rightB),
                  listAppendAssoc mid' [smallerB, biggerB] rightB]
            rw [hsrc, ← htgt]
            exact OmegacEWord.RewritesMany.single step

/-- **The sorting system is locally confluent.**  Decompose both one-step reducts of a common source, then by the
redex-position comparison apply `sortingJoinableWhenLeftShorter` (or its symmetric). -/
theorem sortingHasLocalConfluence {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) :
    HasLocalConfluence (sortingSystem slotValue) := by
  intro sourceWord firstReduct secondReduct step1 step2
  obtain ⟨leftA, rightA, biggerA, smallerA, hA, hSrcA, hTgtA⟩ :=
    sortingRewriteOneStep_decomposition slotValue step1
  obtain ⟨leftB, rightB, biggerB, smallerB, hB, hSrcB, hTgtB⟩ :=
    sortingRewriteOneStep_decomposition slotValue step2
  have hEq : leftA ++ [biggerA, smallerA] ++ rightA
           = leftB ++ [biggerB, smallerB] ++ rightB := hSrcA.symm.trans hSrcB
  have hFirst : firstReduct = ⟨leftA ++ [smallerA, biggerA] ++ rightA⟩ := by rw [← hTgtA]
  have hSecond : secondReduct = ⟨leftB ++ [smallerB, biggerB] ++ rightB⟩ := by rw [← hTgtB]
  rw [hFirst, hSecond]
  rcases Nat.le_total leftA.length leftB.length with hle | hle
  · exact sortingJoinableWhenLeftShorter slotValue leftA rightA leftB rightB
      biggerA smallerA biggerB smallerB hA hB hEq hle
  · exact (sortingJoinableWhenLeftShorter slotValue leftB rightB leftA rightA
      biggerB smallerB biggerA smallerA hB hA hEq.symm hle).symm

/-- **The sorting system is CONFLUENT** — the SN-120 confluence headline.  `newman` applied to the local
confluence here plus the shipped `sortingSystem_isTerminating`: termination + local confluence ⟹ global
confluence.  The bubble-sort / symmetric-group presentation is convergent; the only remaining SN-120 atom is the
decidable word problem (the guarded `WordReducer`). -/
theorem sortingHasConfluence {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat) :
    HasConfluence (sortingSystem slotValue) :=
  newman (sortingHasLocalConfluence slotValue) (sortingSystem_isTerminating slotValue)

end FX1Poly.OmegacE
