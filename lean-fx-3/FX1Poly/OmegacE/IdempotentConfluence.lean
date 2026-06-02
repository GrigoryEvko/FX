import FX1Poly.OmegacE.IdempotentReducer

/-! # FX1Poly/OmegacE/IdempotentConfluence
    — the confluence layer for the idempotent system `[c,c] → [c]`: structural characterization of one-step
    rewriting (the critical-pair extraction tool)

`IdempotentReducer.lean` shipped the reducer + terminating normalizer.  The remaining piece for the decidable
word problem (`decidableConvertibleModulo_ofConvergent`) is `HasLocalConfluence` — the critical-pair check.
This file opens that layer with the STRUCTURAL CHARACTERIZATION of one-step idempotent rewriting:

    `RewritesOneStep (idempotentSystem cell) source target ↔
       ∃ A B, source.cells = A ++ [cell, cell] ++ B ∧ target.cells = A ++ [cell] ++ B`

i.e. a rewrite is exactly "collapse one `[c,c]` occurrence to `[c]` in some context."  This is the inversion
that turns the inductive `RewritesOneStep` (fire / left-context / right-context) into an explicit redex
position — the form the overlap (critical-pair) analysis for local confluence consumes.

* `rewriteOneStep_decomposition` — forward (every rewrite has such a decomposition; induction on the rewrite,
  the context constructors extend `A`/`B`).
* `rewriteOneStep_ofDecomposition` — backward (any such decomposition IS a rewrite; `fire` under both contexts).

Plus the propext-free list-surgery helper `listAppendAssoc` (core `List.append_assoc` carries propext in this
Init-only setting — the Word.lean discipline).

From the characterization, this file CLOSES the decidable word problem:

* `listPrefixSplit` — the shorter of two prefixes extends to the longer by a `mid` that heads the rest (the
  combinatorial core of overlap analysis).
* `joinableWhenLeftShorter` — given two redex decompositions of one word with the left one shorter, the reducts
  are joinable.  The three overlap cases on `mid`: `[]` and `[c]` collapse to `firstReduct = secondReduct`
  (joinable by reflexivity); `c :: c :: mid'` is the disjoint case where both reducts fire the OTHER redex to a
  common word in one step each.
* `idempotentHasLocalConfluence` — `HasLocalConfluence` by trichotomy (`Nat.le_total`) over the two redex
  positions, applying `joinableWhenLeftShorter` or its symmetric.
* `decidableConvertibleModulo_idempotentSystem` — **the payoff**: `decidableConvertibleModulo_ofConvergent`
  (local confluence + the shipped termination + the shipped reducer) ⟹ the idempotent system's word problem is
  DECIDABLE.  The FIRST non-trivial fully-decided ωcE system — `newman` + the convergent-presentation decision
  validated end-to-end on a real, genuinely-rewriting presentation.

## Zero-axiom verification

`listAppendAssoc`/`listAppendNil` are structural list inductions (`List.cons_append`/`List.nil_append` are
propext-free; `List.append_assoc`/`List.append_nil` are NOT, so we avoid them).  CRITICAL: `simp` — even
`simp only` with propext-free lemmas — pulls `propext` via its congruence/closing machinery, so ALL list-equality
reasoning here is `rw`-only, using `singleConsAppend`/`doubleConsAppend` (`rfl` lemmas collapsing `[c]++`/`[c,c]++`
redexes, which also keep `injection` from leaking `[].append` artifacts) + explicit-argument `listAppendAssoc`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- **Propext-free list-append associativity.**  Core `List.append_assoc` carries `propext` in this Init-only
setting; this structural proof (via the propext-free `List.cons_append`) does not. -/
theorem listAppendAssoc {α : Type _} : ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | _ :: xs', ys, zs => by
      rw [List.cons_append, List.cons_append, List.cons_append, listAppendAssoc xs' ys zs]

/-- **Forward characterization**: every one-step idempotent rewrite collapses one `[c,c]` to `[c]` in some
left/right context — `source = A ++ [c,c] ++ B`, `target = A ++ [c] ++ B`.  By induction on the rewrite: `fire`
is the empty-context base; the context constructors extend `A` (left) or `B` (right), re-associated via
`listAppendAssoc`. -/
theorem rewriteOneStep_decomposition {dimension : Nat} (cell : OmegacECell dimension) :
    ∀ {source target : OmegacEWord dimension},
      OmegacEWord.RewritesOneStep (idempotentSystem cell) source target →
      ∃ leftPart rightPart,
        source.cells = leftPart ++ [cell, cell] ++ rightPart ∧
        target.cells = leftPart ++ [cell] ++ rightPart := by
  intro source target step
  induction step with
  | fire rule isInSystem =>
      have ruleEq : rule = idempotentRule cell := isInSystem
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

/-- **Backward characterization**: any `A ++ [c,c] ++ B → A ++ [c] ++ B` IS a one-step idempotent rewrite —
`fire` (`idempotentRule_fires`) under the right context `B` then the left context `A`. -/
theorem rewriteOneStep_ofDecomposition {dimension : Nat} (cell : OmegacECell dimension)
    (leftPart rightPart : List (OmegacECell dimension)) :
    OmegacEWord.RewritesOneStep (idempotentSystem cell)
      ⟨leftPart ++ [cell, cell] ++ rightPart⟩ ⟨leftPart ++ [cell] ++ rightPart⟩ := by
  have fired : OmegacEWord.RewritesOneStep (idempotentSystem cell)
      ⟨leftPart ++ ([cell, cell] ++ rightPart)⟩ ⟨leftPart ++ ([cell] ++ rightPart)⟩ :=
    OmegacEWord.RewritesOneStep.underLeftContext ⟨leftPart⟩
      (OmegacEWord.RewritesOneStep.underRightContext ⟨rightPart⟩ (idempotentRule_fires cell))
  rw [← listAppendAssoc, ← listAppendAssoc] at fired
  exact fired

/-- Propext-free `xs ++ [] = xs` (core `List.append_nil` carries propext). -/
theorem listAppendNil {α : Type _} : ∀ (xs : List α), xs ++ [] = xs
  | [] => rfl
  | _ :: xs' => by rw [List.cons_append, listAppendNil xs']

/-- `[a] ++ rest = a :: rest` definitionally — collapses a singleton-append redex without `injection`
artifacts. -/
theorem singleConsAppend {α : Type _} (a : α) (rest : List α) : [a] ++ rest = a :: rest := rfl

/-- `[a, b] ++ rest = a :: b :: rest` definitionally — collapses the `[c,c]` redex cleanly. -/
theorem doubleConsAppend {α : Type _} (a b : α) (rest : List α) :
    [a, b] ++ rest = a :: b :: rest := rfl

/-- **Prefix split**: if `firstPrefix ++ firstRest = secondPrefix ++ secondRest` and `firstPrefix` is the
shorter prefix, the longer prefix extends it by a `mid` that heads `firstRest`.  The combinatorial core of the
overlap analysis. -/
theorem listPrefixSplit {α : Type _} :
    ∀ (firstPrefix secondPrefix firstRest secondRest : List α),
      firstPrefix ++ firstRest = secondPrefix ++ secondRest →
      firstPrefix.length ≤ secondPrefix.length →
      ∃ mid, secondPrefix = firstPrefix ++ mid ∧ firstRest = mid ++ secondRest
  | [], secondPrefix, firstRest, secondRest, hEq, _ =>
      ⟨secondPrefix, rfl, hEq⟩
  | _ :: firstPrefix', [], _, _, _hEq, hLen =>
      absurd hLen (Nat.not_succ_le_zero firstPrefix'.length)
  | first :: firstPrefix', second :: secondPrefix', firstRest, secondRest, hEq, hLen => by
      injection hEq with hHead hTail
      have hLen' : firstPrefix'.length ≤ secondPrefix'.length :=
        Nat.le_of_succ_le_succ hLen
      obtain ⟨mid, hMid, hRest⟩ :=
        listPrefixSplit firstPrefix' secondPrefix' firstRest secondRest hTail hLen'
      exact ⟨mid, by rw [hMid, List.cons_append, hHead], hRest⟩

/-- Word joinability from word equality (the joining point is the common word). -/
theorem joinable_of_wordEq {dimension : Nat} {system : OmegacERewriteRule dimension → Prop}
    {firstWord secondWord : OmegacEWord dimension} (h : firstWord = secondWord) :
    OmegacEWord.Joinable system firstWord secondWord := by
  rw [h]; exact OmegacEWord.Joinable.refl secondWord

/-- **When the left redex is the shorter prefix, the two reducts are joinable.**  Prefix-split, then case on the
overlap `mid`: `[]` (same redex) and `[c]` (one-cell overlap, `[c,c,c]`) both give `firstReduct = secondReduct`;
`c :: c :: mid'` is disjoint — each reduct fires the other (still-present) redex, meeting at a common word. -/
theorem joinableWhenLeftShorter {dimension : Nat} (cell : OmegacECell dimension)
    (leftA rightA leftB rightB : List (OmegacECell dimension))
    (hEq : leftA ++ [cell, cell] ++ rightA = leftB ++ [cell, cell] ++ rightB)
    (hLen : leftA.length ≤ leftB.length) :
    OmegacEWord.Joinable (idempotentSystem cell)
      ⟨leftA ++ [cell] ++ rightA⟩ ⟨leftB ++ [cell] ++ rightB⟩ := by
  rw [listAppendAssoc, listAppendAssoc] at hEq
  obtain ⟨mid, hMid, hRest⟩ :=
    listPrefixSplit leftA leftB ([cell, cell] ++ rightA) ([cell, cell] ++ rightB) hEq hLen
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
          injection hRest with hm hRest1
          injection hRest1 with _ hRights
          subst hm
          subst hRights
          subst hMid
          apply joinable_of_wordEq
          apply congrArg OmegacEWord.mk
          rw [listAppendAssoc (leftA ++ [cell]) [cell] rightB, singleConsAppend]
      | cons m2 mid' =>
          rw [List.cons_append, List.cons_append] at hRest
          injection hRest with hm1 hRest1
          injection hRest1 with hm2 hRights
          subst hm1
          subst hm2
          subst hRights
          subst hMid
          refine ⟨⟨leftA ++ [cell] ++ mid' ++ [cell] ++ rightB⟩, ?_, ?_⟩
          · have step := rewriteOneStep_ofDecomposition cell (leftA ++ [cell] ++ mid') rightB
            have hsrc :
                (⟨leftA ++ [cell] ++ (mid' ++ (cell :: cell :: rightB))⟩ : OmegacEWord dimension) =
                  ⟨leftA ++ [cell] ++ mid' ++ [cell, cell] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc (leftA ++ [cell] ++ mid') [cell, cell] rightB, doubleConsAppend,
                  listAppendAssoc (leftA ++ [cell]) mid' (cell :: cell :: rightB)]
            rw [hsrc]
            exact OmegacEWord.RewritesMany.single step
          · have step := rewriteOneStep_ofDecomposition cell leftA (mid' ++ [cell] ++ rightB)
            have hsrc :
                (⟨leftA ++ cell :: cell :: mid' ++ [cell] ++ rightB⟩ : OmegacEWord dimension) =
                  ⟨leftA ++ [cell, cell] ++ (mid' ++ [cell] ++ rightB)⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc (leftA ++ cell :: cell :: mid') [cell] rightB,
                  listAppendAssoc leftA (cell :: cell :: mid') ([cell] ++ rightB),
                  listAppendAssoc leftA [cell, cell] (mid' ++ [cell] ++ rightB),
                  doubleConsAppend, listAppendAssoc mid' [cell] rightB,
                  List.cons_append, List.cons_append]
            have htgt :
                (⟨leftA ++ [cell] ++ (mid' ++ [cell] ++ rightB)⟩ : OmegacEWord dimension) =
                  ⟨leftA ++ [cell] ++ mid' ++ [cell] ++ rightB⟩ := by
              apply congrArg OmegacEWord.mk
              rw [listAppendAssoc mid' [cell] rightB,
                  listAppendAssoc (leftA ++ [cell] ++ mid') [cell] rightB,
                  listAppendAssoc (leftA ++ [cell]) mid' ([cell] ++ rightB)]
            rw [hsrc, ← htgt]
            exact OmegacEWord.RewritesMany.single step

/-- **The idempotent system is locally confluent.**  Decompose both one-step reducts of a common source, then
by trichotomy on the two redex positions apply `joinableWhenLeftShorter` (or its symmetric). -/
theorem idempotentHasLocalConfluence {dimension : Nat} (cell : OmegacECell dimension) :
    HasLocalConfluence (idempotentSystem cell) := by
  intro sourceWord firstReduct secondReduct step1 step2
  obtain ⟨leftA, rightA, hSrcA, hTgtA⟩ := rewriteOneStep_decomposition cell step1
  obtain ⟨leftB, rightB, hSrcB, hTgtB⟩ := rewriteOneStep_decomposition cell step2
  have hEq : leftA ++ [cell, cell] ++ rightA = leftB ++ [cell, cell] ++ rightB :=
    hSrcA.symm.trans hSrcB
  have hFirst : firstReduct = ⟨leftA ++ [cell] ++ rightA⟩ := by rw [← hTgtA]
  have hSecond : secondReduct = ⟨leftB ++ [cell] ++ rightB⟩ := by rw [← hTgtB]
  rw [hFirst, hSecond]
  rcases Nat.le_total leftA.length leftB.length with hle | hle
  · exact joinableWhenLeftShorter cell leftA rightA leftB rightB hEq hle
  · exact (joinableWhenLeftShorter cell leftB rightB leftA rightA hEq.symm hle).symm

/-- **The idempotent system's word problem is decidable** — the FIRST non-trivial fully-decided ωcE system.
Composes the discharged local confluence + the shipped termination + the shipped reducer through the
convergent-presentation decision (`newman` → `toNormalizer` → `decidableOfNormalizer`). -/
def decidableConvertibleModulo_idempotentSystem {dimension : Nat} (cell : OmegacECell dimension)
    (firstWord secondWord : OmegacEWord dimension) :
    Decidable (OmegacEWord.ConvertibleModulo (idempotentSystem cell) firstWord secondWord) :=
  decidableConvertibleModulo_ofConvergent (idempotentHasLocalConfluence cell)
    (idempotentSystem_isTerminating cell) (idempotentWordReducer cell) firstWord secondWord

end FX1Poly.OmegacE
