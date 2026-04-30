import LeanFX.Syntax.CdDominates

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `cd_lemma`: every parallel reduct lands in `Term.cd`.

`Step.par.cd_lemma : Step.par t t' → Step.par t' (Term.cd t)` is the
second half of the Tait–Martin-Löf complete-development pair.  Given
the `cd_dominates` lemma `Step.par t (Term.cd t)`, cd_lemma closes the
diamond: any single parallel step from `t` to `t'` can be matched by a
parallel step from `t'` to `cd t`.

The proof is by induction on the Step.par derivation.  For each
constructor:

- `refl t`: `t' = t`, so we use `cd_dominates t`.
- Constructor wrappers (cong): the rhs is a smaller cong, so we
  recurse and rebuild via the corresponding `Step.par` ctor.  For
  eliminator cong rules, we additionally need to show that cd's
  contraction at the redex shape matches the IH's witness.
- β/ι rules (shallow): the rhs is the contracted form; cd contracts
  the same redex, so `Step.par.subst_compatible` (β) or the IH (ι)
  closes.
- Deep rules: the inner premise is `Step.par x (TargetCtor ...)`, so
  IH gives `Step.par (TargetCtor ...) (cd x)`.  Inversion on the
  resulting parallel step yields `cd x = TargetCtor ...'` where `...'`
  is a parallel reduct, which is exactly the shape cd's eliminator
  case fires on. -/

/-! ### Inversion lemmas — what shapes can `Step.par t (Ctor ...)` take?

Each inversion lemma states: when `Step.par X (Term.Ctor args)` holds
(where Ctor is a constructor and args some sub-derivation pattern),
the rhs Y of `Step.par Y X` is itself `Term.Ctor args'` with a
related parallel-step relation between the args/args'.  This is what
the deep cd_lemma cases need to break out of generic `Step.par`. -/

-- TODO: inversion lemmas (Step.par.lam_inv, lamPi_inv, pair_inv,
-- refl_inv, boolTrue_inv, boolFalse_inv, natZero_inv, natSucc_inv,
-- listNil_inv, listCons_inv, optionNone_inv, optionSome_inv,
-- eitherInl_inv, eitherInr_inv).  Phase 4 will add them as needed.

end LeanFX.Syntax
