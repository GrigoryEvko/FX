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

## Honest scope

This is the characterization, NOT yet local confluence.  `HasLocalConfluence` needs: from two decompositions
of one word, a prefix split + case analysis on the overlap (the only critical pair is `[c,c,c]`, reducing to
`[c,c]` via BOTH firings — joinable at `[c,c]`; disjoint redexes commute in one step each).  That overlap proof
+ `newman` + the shipped normalizer ⟹ `decidableConvertibleModulo_ofConvergent` — the next Path-B atom, for
which this characterization is the foundation.

## Zero-axiom verification

`listAppendAssoc` is structural list induction (`List.cons_append` is propext-free; `List.append_assoc` is
NOT, so we avoid it).  The characterization is induction on `RewritesOneStep` + `listAppendAssoc` re-association
(NOT core `List.append_assoc`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditOmegacE.lean`.
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

end FX1Poly.OmegacE
