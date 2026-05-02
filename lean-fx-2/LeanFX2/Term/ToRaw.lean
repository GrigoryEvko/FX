import LeanFX2.Term

/-! # Term/ToRaw — projection (collapsed to rfl)

In lean-fx, `Term.toRaw` was a 53-line structural recursion plus
~10 supporting lemmas (`Term.toRaw_cast`, `Term.toRaw_rename`,
`Term.toRaw_subst`, `Term.toRaw_subst0`, `Term.toRaw_subst0_term`,
etc.).  In lean-fx-2, raw IS the type index — these collapse.

## Contents

* `Term.toRaw : Term ctx ty raw → RawTerm scope := raw` (the index
  projection; defined `@[reducible]` so it's transparent).
* `Term.toRaw_var i : Term.toRaw (Term.var i) = RawTerm.var i := rfl`
* `Term.toRaw_unit : Term.toRaw Term.unit = RawTerm.unit := rfl`
* `Term.toRaw_lam body : Term.toRaw (Term.lam body) = RawTerm.lam (Term.toRaw body) := rfl`
* `Term.toRaw_app fn arg : Term.toRaw (Term.app fn arg) = RawTerm.app fn.toRaw arg.toRaw := rfl`
* ... all constructors, all `rfl`
* `Term.toRaw_rename ρt t : Term.toRaw (Term.rename ρt t) = (Term.toRaw t).rename ρ := rfl`
  (raw index propagates via Term.rename's signature)
* `Term.toRaw_subst σ t : Term.toRaw (Term.subst σ t) = (Term.toRaw t).subst σ.forRaw := rfl`
* `Term.toRaw_subst0 body arg : Term.toRaw (Term.subst0 body arg) = body.toRaw.subst0 arg.toRaw := rfl`

## Why these lemmas exist as named decls (not just `rfl`)

Even though they're rfl, named lemmas give:
1. Discoverability — searching for "toRaw_subst" finds the
   computation rule
2. Simp lemma usability — `simp only [Term.toRaw_subst]` rewrites
   bridging proofs
3. Documentation — the file enumerates the projection's behavior
   on every constructor

## Diff from lean-fx

* `Term.toRaw_cast` — DELETED (cast doesn't affect raw index)
* `Term.toRaw_subst0_term` — DELETED (subst0 and subst0_term unify)
* `Term.subst0_term_subst_HEq` — DELETED (no RawConsistent, no
  subst0_term variant)
* `TermSubst.RawConsistent` — DELETED entirely

## Dependencies

* `Term.lean` — the inductive

## Downstream consumers

* `Bridge.lean` — the typed→raw bridge uses these as rfl hints
* `Reduction/RawPar.lean` — connects via toRaw projections
-/

namespace LeanFX2

end LeanFX2
