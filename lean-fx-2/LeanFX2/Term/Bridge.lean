import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.ToRaw

/-! # Term/Bridge — projection commutes with rename / subst

The headline lemmas:

```lean
theorem Term.toRaw_rename : (Term.rename ρ t).toRaw = (Term.toRaw t).rename ρ
theorem Term.toRaw_subst  : (Term.subst σ t).toRaw  = (Term.toRaw t).subst σ.forRaw
```

In lean-fx-2's raw-aware Term encoding, both are `rfl` — the typed
`Term.rename` produces a term whose raw index IS the renamed raw, by
construction of the inductive's third index.

In lean-fx (without raw-aware Term), `Term.toRaw_rename` was a 50+
line structural induction over Term, paralleling Term.rename's
recursion at the raw level.  The raw-aware encoding collapses the
proof to `rfl`.

These are the foundational bridge lemmas: ALL bridge proofs (typed
reduction → raw reduction) start with `rw [Term.toRaw_rename, ...]`
to reduce to a raw-level claim.

## Why isolate from `Term/ToRaw.lean`

`Term/ToRaw.lean` only proves per-ctor projection lemmas (each one
matching the constructor's raw payload).  The rename/subst commutes
require importing `Term/Rename.lean` + `Term/Subst.lean`, which depend
on `Term/ToRaw.lean`'s definition of toRaw.  Keeping them separate
preserves the layered import graph.
-/

namespace LeanFX2

/-- Projection commutes with renaming.  The Term.rename of `t` has
type-index `raw.rename ρ`, so `(rename t).toRaw = raw.rename ρ`
which equals `t.toRaw.rename ρ`.  Both sides reduce to the same
literal — `rfl`. -/
theorem Term.toRaw_rename {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (someTerm : Term sourceCtx someType raw) :
    (Term.rename termRenaming someTerm).toRaw = someTerm.toRaw.rename rho := rfl

/-- Projection commutes with substitution.  Same reasoning as
toRaw_rename: the type-index pins the raw side, so projection is
literally rewriting the index. -/
theorem Term.toRaw_subst {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {someType : Ty level sourceScope} {raw : RawTerm sourceScope}
    (someTerm : Term sourceCtx someType raw) :
    (Term.subst termSubst someTerm).toRaw = someTerm.toRaw.subst sigma.forRaw := rfl

/-- Projection commutes with the convenience wrapper `Term.weaken`. -/
theorem Term.toRaw_weaken {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {someType : Ty level scope}
    {raw : RawTerm scope} (newType : Ty level scope)
    (someTerm : Term context someType raw) :
    (Term.weaken newType someTerm).toRaw = someTerm.toRaw.weaken := rfl

/-- Projection commutes with `Term.subst0`.  The β-redex contractum's
raw side equals the source body's raw substituted by the argument's
raw — by construction of the `subst0` definition. -/
theorem Term.toRaw_subst0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {substituent : Ty level scope} {argRaw : RawTerm scope}
    {codomainType : Ty level (scope + 1)} {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm : Term (context.cons substituent) codomainType bodyRaw)
    (argTerm : Term context substituent argRaw) :
    (Term.subst0 bodyTerm argTerm).toRaw = bodyRaw.subst0 argRaw := rfl

end LeanFX2
