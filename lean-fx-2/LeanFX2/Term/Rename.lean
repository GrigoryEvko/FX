import LeanFX2.Term

/-! # Term/Rename — typed renaming

`Term.rename` propagates the raw index automatically:

```lean
def Term.rename {m scope scope'}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'}
    (ρt : TermRenaming Γ Δ ρ) :
    {T : Ty level scope} → {raw : RawTerm scope} →
    Term Γ T raw → Term Δ (T.rename ρ) (raw.rename ρ)
```

The output Term has raw `raw.rename ρ` — automatic via index
propagation.  Each match arm constructs a new Term whose raw is
recursively renamed.

## Contents

* `Term.rename` — typed renaming, structural induction
* `Term.weaken (newType : Ty level scope) (term : Term Γ T raw) :
  Term (Γ.cons newType) T.weaken raw.weaken` — single-binder
  weakening, derived as `Term.rename (TermRenaming.weaken Γ newType)`

## Match-arm patterns

Most constructors use the recursive call's auto-elaborated raw index:

```lean
| _, _, .lam body =>
    Term.lam (Term.rename (TermRenaming.lift ρt _) body)
-- bodyRaw_renamed propagates from inner body's raw
```

For the `.var i` case, the cast is from `varType Γ i` to
`varType Δ (ρ i)` via `ρt i`'s position equality:

```lean
| _, _, .var i => (ρt i) ▸ Term.var (ρ i)
```

Identity types' `refl rawTerm` carries an explicit raw witness:

```lean
| _, _, .refl rawTerm => Term.refl (rawTerm.rename ρ)
-- Result: Term Δ (Ty.id (carrier.rename ρ) (rawTerm.rename ρ) (rawTerm.rename ρ))
--                (RawTerm.refl (rawTerm.rename ρ))
-- Index propagates correctly.
```

## Lawfulness

* `Term.rename_identity` — renaming by identity is identity (with
  appropriate Ctx-mapping)
* `Term.rename_compose` — composition law
* `Term.toRaw_rename : (Term.rename ρt t).toRaw = t.toRaw.rename ρ`
  is **`rfl`** — the raw index propagates definitionally

## Dependencies

* `Term.lean` — the inductive

## Downstream consumers

* `Term/Subst.lean` — TermSubst.lift uses Term.weaken
* `Reduction/Rename.lean` — Step.rename_compatible uses Term.rename

## Implementation plan (Phase 2)

Port from `lean-fx/LeanFX/Syntax/TypedTerm.lean` lines 332-454, with
modifications:
* Drop the W9.B1.1/B1.2 `resultEq` parameter handling (no longer
  exists in lean-fx-2's appPi/snd)
* Add raw index propagation per the sketch's pattern
* Verify `Term.toRaw_rename = rfl` (no separate proof needed)

Total: ~80-100 lines target.
-/

namespace LeanFX2

end LeanFX2
