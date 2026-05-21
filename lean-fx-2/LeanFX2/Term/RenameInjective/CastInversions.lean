import LeanFX2.Term.RenameInjective.ConstructorFamilies
import LeanFX2.Term.RenameInjective.BinderInversions
import LeanFX2.Term.TypedInversion

/-! # Term/RenameInjective/CastInversions

HEq-aware destructors for typed terms whose result type carries a `Ty.subst0`
cast (so the matcher cannot align the outer type via simple unification).

The three destructors here mirror the `Term.lam_arrow_inv` / `Term.lam_pi_inv`
pattern in `BinderInversions.lean`: a `_raw_inv` lemma decomposes a typed
term whose raw is a fixed shape into a PSum over every ctor producing that
raw, then a typed-at-fixed-outer-type wrapper filters to the relevant branch
and discharges sibling collisions.

These unblock the `appPi`, `snd`, and `boolElim` arms in
`InductiveArms.lean`.  All zero-axiom.
-/

namespace LeanFX2

/-! ## `Term.snd_raw_inv` — single-ctor inversion (no raw collision). -/

def Term.snd_raw_inv
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {pairRaw : RawTerm scope}
    {genericType : Ty level scope}
    (someTerm : Term sourceCtx genericType (RawTerm.snd pairRaw)) :
    Σ' (firstTypeB : Ty level scope)
       (secondTypeB : Ty level (scope + 1))
       (pairB : Term sourceCtx (Ty.sigmaTy firstTypeB secondTypeB) pairRaw)
       (_ : genericType =
           secondTypeB.subst0 firstTypeB (RawTerm.fst pairRaw)),
       HEq someTerm (Term.snd pairB) := by
  cases someTerm
  rename_i firstTypeB secondTypeB pairTermB
  exact ⟨firstTypeB, secondTypeB, pairTermB, rfl, HEq.rfl⟩

/-! ## `Term.appPi_raw_inv` — `RawTerm.app fnRaw argRaw` collides between
    `Term.app` and `Term.appPi`.  Re-export `Term.app_inv` for symmetry. -/

/-- Alias of `Term.app_inv` for naming consistency with the cast-inversion
    family.  See `Term/TypedInversion.lean` for the original definition. -/
@[reducible] def Term.appPi_raw_inv := @Term.app_inv

/-! ## `Term.boolElim_raw_inv` — single-ctor inversion (no raw collision). -/

def Term.boolElim_raw_inv
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {genericType : Ty level scope}
    (someTerm :
      Term sourceCtx genericType
        (RawTerm.boolElim scrutineeRaw thenRaw elseRaw)) :
    Σ' (motiveTypeB : Ty level (scope + 1))
       (scrutineeB : Term sourceCtx Ty.bool scrutineeRaw)
       (thenBranchB :
         Term sourceCtx (motiveTypeB.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
       (elseBranchB :
         Term sourceCtx (motiveTypeB.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
       (_ : genericType = motiveTypeB.subst0 Ty.bool scrutineeRaw),
       HEq someTerm
         (Term.boolElim scrutineeB thenBranchB elseBranchB) := by
  cases someTerm
  rename_i motiveTypeB scrutineeB thenBranchB elseBranchB
  exact ⟨motiveTypeB, scrutineeB, thenBranchB, elseBranchB, rfl, HEq.rfl⟩

end LeanFX2
