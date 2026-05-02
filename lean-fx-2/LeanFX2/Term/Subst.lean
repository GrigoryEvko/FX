import LeanFX2.Term.Rename

/-! # Term/Subst — typed substitution algebra

`TermSubst` and `Term.subst`.  Raw indices propagate naturally
through substitution because the TermSubst's underlying Subst's
`forRaw` is constrained to match the Term values' raw indices at
each position.

## TermSubst type

```lean
def TermSubst {m level} (sourceCtx : Ctx m level source)
    (targetCtx : Ctx m level target)
    (typeSubst : Subst level source target) : Type :=
  ∀ (i : Fin source),
    Term targetCtx ((varType sourceCtx i).subst typeSubst)
                   (typeSubst.forRaw i)
```

Each position maps to a Term whose raw form equals
`typeSubst.forRaw i`.  This **constrains** TermSubst — you can't
construct one without committing to the raw forms via the underlying
Subst's forRaw.  No `RawConsistent` side condition needed; it's
structural.

## Term.subst signature

```lean
def Term.subst (σ : TermSubst sourceCtx targetCtx typeSubst) :
    {ty : Ty level scope} → {raw : RawTerm scope} →
    Term sourceCtx ty raw →
    Term targetCtx (ty.subst typeSubst) (raw.subst typeSubst.forRaw)
```

Output's raw is `raw.subst typeSubst.forRaw` — the typed and raw
substitutions stay synchronized by construction.

## Term.subst0 — single-binder substitution

```lean
def Term.subst0 {m level scope} {sourceCtx : Ctx m level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope+1)}
    {bodyRaw : RawTerm (scope+1)} {argRaw : RawTerm scope}
    (body : Term (sourceCtx.cons argType) bodyType bodyRaw)
    (arg : Term sourceCtx argType argRaw) :
    Term sourceCtx (bodyType.subst (Subst.singleton argType argRaw))
                   (bodyRaw.subst0 argRaw)
```

**One** subst0 operation.  No `subst0_term` variant.  No `RawConsistent`.
The `argRaw` index of the result is automatically `bodyRaw.subst0
argRaw` via raw-aware Term's index propagation.

## TermSubst constructors

* `TermSubst.identity` — at every position, `Term.var i`
* `TermSubst.singleton (arg : Term sourceCtx argType argRaw)
  : TermSubst (sourceCtx.cons argType) sourceCtx
    (Subst.singleton argType argRaw)` — UNIFIED single-binder
  TermSubst.  Each position's Term has raw matching the Subst's
  forRaw.
* `TermSubst.lift (σ : TermSubst Γ Δ s) (newType : Ty)
  : TermSubst (Γ.cons newType) (Δ.cons (newType.subst s)) s.lift`
* `TermSubst.compose : TermSubst Γ Δ s1 → TermSubst Δ Φ s2
  → TermSubst Γ Φ (s1.compose s2)`

## Lawfulness

Most lemmas collapse to `rfl` or trivial structural induction:
* `Term.subst_identity`
* `Term.subst_compose`
* `Term.subst0_subst_HEq` — single-binder + outer subst commute
* `Term.toRaw_subst : (Term.subst σ t).toRaw = t.toRaw.subst σ.forRaw`
  is **`rfl`** (index propagation)

## Why `RawConsistent` is gone

In lean-fx, `TermSubst.RawConsistent σ` was a side condition: at
every position, the TermSubst's Term value's `Term.toRaw` had to
equal the underlying Subst's `forRaw` at that position.  This was
needed because lean-fx's TermSubst structure didn't enforce the
constraint at definition time.

In lean-fx-2, the TermSubst type IS the constraint (the Term
value's raw index must equal `typeSubst.forRaw i`).  No proof
obligation, no side condition, no threading through theorems.

## Dependencies

* `Term/Rename.lean` — TermSubst.lift uses Term.weaken (= rename)

## Downstream consumers

* `Term/Pointwise.lean` — pointwise lemmas about TermSubst
* `Reduction/Subst.lean` — Step.subst_compatible
* `Confluence/Cd.lean` — Term.cd uses subst0 in β-arms

## Implementation plan (Phase 2)

1. Define TermSubst as a function type with raw constraint baked in
2. Define Term.subst by structural recursion on Term
3. Define Term.subst0 as a wrapper using TermSubst.singleton
4. Lawfulness lemmas (subst_identity, subst_compose, etc.)
5. Drop all `subst0_term`-flavor lemmas (no longer exist)
6. Drop `RawConsistent` and its lemmas

Total: ~150-200 lines (vs ~500 lines in lean-fx's TermSubst/* files).
-/

namespace LeanFX2

end LeanFX2
