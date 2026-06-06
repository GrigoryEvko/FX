import FX1Poly.OmegacE.TranspositionSystem
import FX1Poly.OmegacE.IdempotentConfluence

/-! # FX1Poly/OmegacE/TranspositionConfluence
    — the adjacent-transposition system is locally confluent (hence, with termination, CONFLUENT)

`TranspositionSystem.lean` shipped the length-preserving rule `[a,b] → [b,a]` and its TERMINATION (via the
inversion measure).  This file completes the convergence picture: LOCAL CONFLUENCE, and — via Newman's lemma
with the shipped termination — global CONFLUENCE.

The transposition rule has NO self-overlap: an overlap of two `[a,b]` redexes at adjacent positions `i, i+1`
would force `w[i+1] = b` (from the first) and `w[i+1] = a` (from the second), i.e. `a = b`, excluded by
`firstCell ≠ secondCell`.  So unlike the idempotent system (whose `[c,c,c]` self-overlap is a real critical
pair resolved to `[c,c]`), the transposition system is ORTHOGONAL: the only divergences are disjoint redexes,
which commute.  The one-cell-overlap case of the prefix trichotomy is therefore VACUOUS (`absurd`), and local
confluence is "disjoint redexes commute" plus the degenerate same-redex case.

* `transpositionRewriteOneStep_decomposition` / `…_ofDecomposition` — the structural inversion: a one-step
  rewrite is exactly `A ++ [a,b] ++ B ↦ A ++ [b,a] ++ B` for some context `A`, `B` (and conversely).
* `transpositionJoinableWhenLeftShorter` — when the left redex is the shorter prefix, the two reducts are
  joinable: prefix-split, then the `[]` (same redex) / `[m]` (IMPOSSIBLE, `a ≠ b`) / `m :: m2 :: mid'`
  (disjoint, each reduct fires the other still-present redex) trichotomy.
* `transpositionHasLocalConfluence` — local confluence, by decomposing both reducts and dispatching to
  `transpositionJoinableWhenLeftShorter` (or its symmetric) on the redex-position comparison.
* `transpositionHasConfluence` — GLOBAL confluence, `newman` applied to the local confluence here + the shipped
  `transpositionSystem_isTerminating`.  The non-length analogue of `idempotentHasLocalConfluence`'s convergent
  presentation.

## Honest scope

This ships CONFLUENCE (local + global).  The decidable word problem (`decidableConvertibleModulo_ofConvergent`)
additionally needs a `WordReducer (transpositionSystem a b)` — a searchable leftmost-`[a,b]` matcher with
soundness/completeness (mirroring `idempotentWordReducer`) — the next and final atom.

## Zero-axiom verification

The decomposition mirrors `rewriteOneStep_decomposition`; `joinableWhenLeftShorter` mirrors its idempotent
twin, with the one-cell-overlap case discharged by `absurd … distinct` (the no-self-overlap fact).  The
generic word-list helpers (`listAppendAssoc`, `listPrefixSplit`, `doubleConsAppend`, `listAppendNil`,
`joinable_of_wordEq`) are reused from `IdempotentConfluence` (propext-free by construction).  The disjoint-case
word equalities are closed by explicit-argument `rw` chains (NOT `simp only`, which pulls `propext` from its
machinery even over `Eq`-only list lemmas).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- **Structural inversion**: any one-step transposition rewrite is `A ++ [a,b] ++ B ↦ A ++ [b,a] ++ B` for
some context.  By induction on the rewrite derivation (the `fire` case is the bare rule; the context cases
extend the left/right part via `listAppendAssoc`). -/
theorem transpositionRewriteOneStep_decomposition {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell) source target →
      ∃ leftPart rightPart,
        source.cells = leftPart ++ [firstCell, secondCell] ++ rightPart ∧
        target.cells = leftPart ++ [secondCell, firstCell] ++ rightPart := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      have ruleEq : rule = transpositionRule firstCell secondCell := isInSystem
      subst ruleEq
      exact ⟨[], [], rfl, rfl⟩
  | underLeftContext prefixWord _inner innerIH =>
      obtain ⟨leftPart, rightPart, hSrc, hTgt⟩ := innerIH
      refine ⟨prefixWord.cells ++ leftPart, rightPart, ?_, ?_⟩
      · show prefixWord.cells ++ _ = _
        rw [hSrc, ← listAppendAssoc, ← listAppendAssoc]
      · show prefixWord.cells ++ _ = _
        rw [hTgt, ← listAppendAssoc, ← listAppendAssoc]
  | underRightContext suffixWord _inner innerIH =>
      obtain ⟨leftPart, rightPart, hSrc, hTgt⟩ := innerIH
      refine ⟨leftPart, rightPart ++ suffixWord.cells, ?_, ?_⟩
      · show _ ++ suffixWord.cells = _
        rw [hSrc, listAppendAssoc]
      · show _ ++ suffixWord.cells = _
        rw [hTgt, listAppendAssoc]

/-- **Backward characterization**: any `A ++ [a,b] ++ B → A ++ [b,a] ++ B` IS a one-step rewrite (`fire` under
the right then left context). -/
theorem transpositionRewriteOneStep_ofDecomposition {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension)
    (leftPart rightPart : List (OmegacECell dimension)) :
    OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell)
      ⟨leftPart ++ [firstCell, secondCell] ++ rightPart⟩
      ⟨leftPart ++ [secondCell, firstCell] ++ rightPart⟩ := by
  have fired : OmegacEWord.RewritesOneStep (transpositionSystem firstCell secondCell)
      ⟨leftPart ++ ([firstCell, secondCell] ++ rightPart)⟩
      ⟨leftPart ++ ([secondCell, firstCell] ++ rightPart)⟩ :=
    OmegacEWord.RewritesOneStep.underLeftContext ⟨leftPart⟩
      (OmegacEWord.RewritesOneStep.underRightContext ⟨rightPart⟩
        (transpositionRule_fires firstCell secondCell))
  rw [← listAppendAssoc, ← listAppendAssoc] at fired
  exact fired

/-- **When the left redex is the shorter prefix, the two reducts are joinable.**  Prefix-split, then case on
the overlap `mid`: `[]` (same redex ⟹ equal reducts); `[m]` (one-cell overlap — IMPOSSIBLE, would force
`secondCell = firstCell`); `m :: m2 :: mid'` (disjoint redexes — each reduct fires the other still-present
redex, meeting at a common word). -/
theorem transpositionJoinableWhenLeftShorter {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) (distinct : firstCell ≠ secondCell)
    (leftA rightA leftB rightB : List (OmegacECell dimension))
    (hEq : leftA ++ [firstCell, secondCell] ++ rightA
         = leftB ++ [firstCell, secondCell] ++ rightB)
    (hLen : leftA.length ≤ leftB.length) :
    OmegacEWord.Joinable (transpositionSystem firstCell secondCell)
      ⟨leftA ++ [secondCell, firstCell] ++ rightA⟩
      ⟨leftB ++ [secondCell, firstCell] ++ rightB⟩ := by
  rw [listAppendAssoc, listAppendAssoc] at hEq
  obtain ⟨mid, hMid, hRest⟩ :=
    listPrefixSplit leftA leftB ([firstCell, secondCell] ++ rightA)
      ([firstCell, secondCell] ++ rightB) hEq hLen
  rw [doubleConsAppend, doubleConsAppend] at hRest
  cases mid with
  | nil =>
      rw [List.nil_append] at hRest
      injection hRest with _ hRest1
      injection hRest1 with _ hRights
      subst hRights
      subst hMid
      apply joinable_of_wordEq
      apply congrArg OmegacEWord.mk
      rw [listAppendNil]
  | cons m midTail =>
      cases midTail with
      | nil =>
          rw [List.cons_append, List.nil_append] at hRest
          injection hRest with _hm hRest1
          injection hRest1 with hsf _hRights
          exact absurd hsf.symm distinct
      | cons m2 mid' =>
          rw [List.cons_append, List.cons_append] at hRest
          injection hRest with hm1 hRest1
          injection hRest1 with hm2 hRights
          subst hm1
          subst hm2
          subst hRights
          subst hMid
          refine ⟨⟨leftA ++ [secondCell, firstCell] ++ mid' ++ [secondCell, firstCell] ++ rightB⟩,
            ?_, ?_⟩
          · have step := transpositionRewriteOneStep_ofDecomposition firstCell secondCell
              (leftA ++ [secondCell, firstCell] ++ mid') rightB
            have hsrc :
                (⟨leftA ++ [secondCell, firstCell] ++ (mid' ++ (firstCell :: secondCell :: rightB))⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [secondCell, firstCell] ++ mid' ++ [firstCell, secondCell] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc (leftA ++ [secondCell, firstCell] ++ mid') [firstCell, secondCell]
                    rightB, doubleConsAppend,
                  listAppendAssoc (leftA ++ [secondCell, firstCell]) mid'
                    (firstCell :: secondCell :: rightB)]
            rw [hsrc]
            exact OmegacEWord.RewritesMany.single step
          · have step := transpositionRewriteOneStep_ofDecomposition firstCell secondCell
              leftA (mid' ++ [secondCell, firstCell] ++ rightB)
            have hsrc :
                (⟨leftA ++ firstCell :: secondCell :: mid' ++ [secondCell, firstCell] ++ rightB⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [firstCell, secondCell] ++ (mid' ++ [secondCell, firstCell] ++ rightB)⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc leftA [firstCell, secondCell]
                    (mid' ++ [secondCell, firstCell] ++ rightB),
                  doubleConsAppend firstCell secondCell
                    (mid' ++ [secondCell, firstCell] ++ rightB),
                  listAppendAssoc (leftA ++ (firstCell :: secondCell :: mid')) [secondCell, firstCell]
                    rightB,
                  listAppendAssoc leftA (firstCell :: secondCell :: mid')
                    ([secondCell, firstCell] ++ rightB),
                  List.cons_append, List.cons_append,
                  listAppendAssoc mid' [secondCell, firstCell] rightB]
            have htgt :
                (⟨leftA ++ [secondCell, firstCell] ++ (mid' ++ [secondCell, firstCell] ++ rightB)⟩
                  : OmegacEWord dimension)
                = ⟨leftA ++ [secondCell, firstCell] ++ mid' ++ [secondCell, firstCell] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc ((leftA ++ [secondCell, firstCell]) ++ mid') [secondCell, firstCell]
                    rightB,
                  listAppendAssoc (leftA ++ [secondCell, firstCell]) mid'
                    ([secondCell, firstCell] ++ rightB),
                  listAppendAssoc mid' [secondCell, firstCell] rightB]
            rw [hsrc, ← htgt]
            exact OmegacEWord.RewritesMany.single step

/-- **The transposition system is locally confluent** (requires `firstCell ≠ secondCell`).  Decompose both
one-step reducts of a common source, then by the redex-position comparison apply
`transpositionJoinableWhenLeftShorter` (or its symmetric). -/
theorem transpositionHasLocalConfluence {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) (distinct : firstCell ≠ secondCell) :
    HasLocalConfluence (transpositionSystem firstCell secondCell) := by
  intro sourceWord firstReduct secondReduct step1 step2
  obtain ⟨leftA, rightA, hSrcA, hTgtA⟩ :=
    transpositionRewriteOneStep_decomposition firstCell secondCell step1
  obtain ⟨leftB, rightB, hSrcB, hTgtB⟩ :=
    transpositionRewriteOneStep_decomposition firstCell secondCell step2
  have hEq : leftA ++ [firstCell, secondCell] ++ rightA
           = leftB ++ [firstCell, secondCell] ++ rightB := hSrcA.symm.trans hSrcB
  have hFirst : firstReduct = ⟨leftA ++ [secondCell, firstCell] ++ rightA⟩ := by rw [← hTgtA]
  have hSecond : secondReduct = ⟨leftB ++ [secondCell, firstCell] ++ rightB⟩ := by rw [← hTgtB]
  rw [hFirst, hSecond]
  rcases Nat.le_total leftA.length leftB.length with hle | hle
  · exact transpositionJoinableWhenLeftShorter firstCell secondCell distinct
      leftA rightA leftB rightB hEq hle
  · exact (transpositionJoinableWhenLeftShorter firstCell secondCell distinct
      leftB rightB leftA rightA hEq.symm hle).symm

/-- **The transposition system is CONFLUENT** (requires `firstCell ≠ secondCell`) — `newman` applied to the
local confluence here plus the shipped `transpositionSystem_isTerminating`.  Termination + local confluence ⟹
global confluence; the convergence picture for the first length-preserving system is complete (only the
decidable word problem, which needs a `WordReducer`, remains). -/
theorem transpositionHasConfluence {dimension : Nat}
    (firstCell secondCell : OmegacECell dimension) (distinct : firstCell ≠ secondCell) :
    HasConfluence (transpositionSystem firstCell secondCell) :=
  newman (transpositionHasLocalConfluence firstCell secondCell distinct)
    (transpositionSystem_isTerminating firstCell secondCell distinct)

end FX1Poly.OmegacE
