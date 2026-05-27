import LeanFX2.Foundation.PolyCell.Core.GeneratorMetadata

/-! # Foundation/PolyCell/Core/GeneratorChildSpecsDim0
   — fxProfile invariant: every generator's child specs are at dim 0

V2-L3.1 phase D step 31 (2026-05-27).  Ships the **profile-level
invariant** required by the structural induction mutual block:

  > For every `Generator`, every `ChildSpec` in `gen.childSpecs` has
  > `cellDimension = 0`.

## Why this matters

The eventual `PolyCell.rename_dim0` / `subst_dim0` mutual block must
recurse into a spine whose `headSpec.cellDimension` is statically
unknown (the spine type only parametrizes over `List ChildSpec`).  To
collapse the spine's `headBoundary` to `CellBoundary.trivial` via
`CertifiedTermSpine.headAtDim0`, the caller needs a witness that
`headSpec.cellDimension = 0`.

In `fxProfile`, every `ChildSpec` is built from the helpers
`ChildSpec.sameScopeDimZero` and `ChildSpec.underOneBinderDimZero`,
both of which set `cellDimension := 0` by definition (`@[reducible]`).
So the invariant holds by construction — but it must be proved as a
THEOREM, not assumed, to feed downstream proofs.

## Shape

We ship two layers:

  1. **Bool-valued check** `Generator.allChildSpecsDim0` that
     evaluates to `true` for every generator (decidable, computable).
  2. **Prop-valued statement** `Generator.childSpecs_cellDimension_zero`
     proving every spec in a generator's children has dim 0.

Both close by case analysis on the Generator enum (194 ctors).  Each
arm reduces to `rfl` or trivial list membership.

## Zero-axiom verification

`cases gen <;> rfl` is the entire proof for the Bool check.  The Prop
version routes through the Bool check + `List.all_eq_true` (an iff
lemma, propext-free in Lean 4 core).

If `cases gen <;> rfl` proves too slow at scale, we fall back to
per-generator theorems (one per arm, each shipped atomically), which
mirrors the discipline used for per-shape compositional preservations.

## Audit-gated

Each shipped declaration carries an `#assert_no_axioms` gate in
`AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **Bool-valued check: every child spec in a generator's `childSpecs`
list has `cellDimension = 0`.**

Evaluates to `true` for every `Generator` in fxProfile.  The proof of
that fact is the next theorem (`allChildSpecsDim0_eq_true`). -/
def Generator.allChildSpecsDim0 (gen : Generator) : Bool :=
  gen.childSpecs.all (·.cellDimension == 0)

/-- **Universal: the Bool check returns `true` for every Generator.**

Closes by case analysis on the Generator enum (194 ctors).  Each case
reduces to `rfl` because the `ChildSpec` helpers
(`sameScopeDimZero` / `underOneBinderDimZero`) set `cellDimension := 0`
by definition, `@[reducible]` lets the projection unfold, and
`List.all` reduces on literal lists. -/
theorem Generator.allChildSpecsDim0_eq_true (gen : Generator) :
    gen.allChildSpecsDim0 = true := by
  cases gen <;> rfl

/-- **List induction lemma: a Bool-`all` of `cellDimension == 0` that
returns `true` propagates to membership: every member's cellDimension
is `0` as a Prop equation.**

Pure list induction, no `simp`, no `List.all_eq_true` iff (which would
leak propext via Iff-rewrites in some Lean 4 elaboration paths).

The `.head` case reads `Bool.and` directly; the `.tail` case recurses
via `ih`. -/
private theorem ChildSpec.all_dim0_propagates_to_mem
    (childSpecsList : List ChildSpec)
    (hAll : childSpecsList.all (·.cellDimension == 0) = true) :
    ∀ spec ∈ childSpecsList, spec.cellDimension = 0 := by
  induction childSpecsList with
  | nil => intro spec hMem; nomatch hMem
  | cons head tail ih =>
    intro spec hMem
    -- `(head :: tail).all p` reduces to `p head && tail.all p`.
    -- We split via direct case analysis on both Bools.
    have hAllCons : ((head.cellDimension == 0) &&
        tail.all (·.cellDimension == 0)) = true := hAll
    have hHead : (head.cellDimension == 0) = true := by
      cases hHeadCase : head.cellDimension == 0 with
      | true  => rfl
      | false =>
        exfalso
        -- After `cases hHeadCase`, hAllCons in scope has been substituted
        -- (head.cellDimension == 0 := false), so it now reads
        -- (false && tail.all _) = true, which reduces to false = true.
        have hContra : (false && tail.all (·.cellDimension == 0)) = true :=
          hHeadCase ▸ hAllCons
        exact Bool.noConfusion hContra
    have hTail : tail.all (·.cellDimension == 0) = true := by
      cases hTailCase : tail.all (·.cellDimension == 0) with
      | true  => rfl
      | false =>
        exfalso
        have hContra : ((head.cellDimension == 0) && false) = true :=
          hTailCase ▸ hAllCons
        rw [hHead] at hContra
        exact Bool.noConfusion hContra
    cases hMem with
    | head =>
      -- spec = head in this arm.  Case-split on head.cellDimension:
      -- zero ⇒ goal closes by rfl; succ ⇒ hHead contradicts.
      cases hCellDim : head.cellDimension with
      | zero => rfl
      | succ predNat =>
        exfalso
        rw [hCellDim] at hHead
        exact Bool.noConfusion hHead
    | tail _ hTailMem => exact ih hTail spec hTailMem

/-- **Prop-valued universal: every child spec in any generator's
`childSpecs` list has `cellDimension = 0`.**

Combines `allChildSpecsDim0_eq_true` (the Bool fact) with the list-
propagation lemma above.  This is the witness the mutual structural
induction quotes when it needs to invoke `CertifiedTermSpine.headAtDim0`
inside the non-var arm of the cell renamer. -/
theorem Generator.childSpecs_cellDimension_zero (gen : Generator) :
    ∀ spec ∈ gen.childSpecs, spec.cellDimension = 0 :=
  ChildSpec.all_dim0_propagates_to_mem gen.childSpecs
    (Generator.allChildSpecsDim0_eq_true gen)

end LeanFX2.Foundation.PolyCell.Core
