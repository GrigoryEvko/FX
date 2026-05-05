/-! # Refine/Term — refinement intro/elim

Refinements are introduced by bundling a base term with proof of
the predicate; eliminated by projecting (and forgetting the proof).

## Intro

```lean
def Term.refineIntro
    {base : Ty level scope}
    {p : RefinePredicate base}
    (term : Term ctx base raw)
    (proof : p.pred term) :
    Term ctx (Ty.refine base p) raw
```

The proof is a Lean-internal proof when the refinement is
decidable; otherwise an SMT certificate.

## Elim

```lean
def Term.refineElim
    {base : Ty level scope}
    {p : RefinePredicate base}
    (refTerm : Term ctx (Ty.refine base p) raw) :
    Term ctx base raw
```

Project to base.  Forgetting refinement is always legal.

The proof component can be recovered:

```lean
theorem refineProof : p.pred (refineElim refTerm)
```

## Boundary semantics

When `Term.refineIntro` is called at a trust boundary (e.g., from
deserialization, FFI), the runtime emits a validator call.  When
called from a verified-internal path, the proof is supplied at
typecheck time and erased.

## Sub-typing through refinement

```lean
theorem Term.refineWeaken
    {p1 p2 : RefinePredicate base}
    (h : ∀ t, p1.pred t → p2.pred t)
    (term : Term ctx (Ty.refine base p1) raw) :
    Term ctx (Ty.refine base p2) raw
```

If `p1 → p2` then values at `p1` fit `p2` (weaker constraint).

## Dependencies

* `Refine/Ty.lean`
* `Term.lean`

## Downstream

* `Refine/Decidable.lean` — auto-generates intro for decidable preds
* fx_design.md §10 — full refinement semantics

## Implementation plan (Phase 9)

1. Define `Term.refineIntro` and `Term.refineElim` (or as Term ctors)
2. Computation rule: `refineElim (refineIntro t _) = t`
3. Smoke: nat-positive refinement intro/elim/use

Target: ~150 lines.
-/

namespace LeanFX2.Refine

-- TODO Phase 9: refineIntro / refineElim ops
-- TODO Phase 9: subtyping weaken
-- TODO Phase 9: computation rules

end LeanFX2.Refine
