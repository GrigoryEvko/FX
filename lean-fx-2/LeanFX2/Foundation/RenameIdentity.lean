import LeanFX2.Foundation.Ty

/-! # Foundation/RenameIdentity — identity-renaming preserves terms

`RawTerm.rename ρ_id t = t` and `Ty.rename ρ_id T = T`: applying the
identity raw renaming is a no-op.  These are needed for any "identity"
proof at the typed Term level (e.g., `Term.rename id t ≅ t`), and
are foundational for canonical-form lemmas in elaboration / Algo.

## Why not in `Foundation/RawSubst.lean` / `Foundation/Ty.lean`?

These two files focus on the structural `rename` / `subst` definitions
plus the most-used commute lemmas.  Identity-specific lemmas are a
separate concern (they're used in elaboration + proof identity, not in
the kernel reduction itself).  Isolating them keeps the dependency
graph clean: this file ONLY adds rfl-projection identity laws, no new
kernel definitions.

## Lemma chain

1. `RawRenaming.identity_lift_pointwise` — id.lift agrees pointwise with id
2. `RawTerm.rename_identity` — RawTerm structural; uses lift_pointwise + rename_pointwise
3. `Ty.rename_identity` — Ty structural; uses RawTerm.rename_identity for `id` arm + lift_pointwise + Ty.rename_pointwise

Each is zero-axiom because it uses only structural recursion + pointwise
lemmas which are themselves zero-axiom.
-/

namespace LeanFX2

/-! ## RawRenaming.identity is pointwise-equal to its lift

`identity.lift` evaluates pattern-by-pattern on `Fin (n+1)`: position 0
goes to position 0, successor positions go to `Fin.succ` of the
identity at the predecessor.  Both reduce to the input position. -/

theorem RawRenaming.identity_lift_pointwise {scope : Nat} :
    ∀ position, (@RawRenaming.identity scope).lift position = position
  | ⟨0, _⟩     => rfl
  | ⟨_ + 1, _⟩ => rfl

/-! ## RawTerm.rename_identity

Structural induction: var case is rfl.  Binders use the lift_pointwise
lemma to bridge `body.rename identity.lift` to `body.rename identity`
via `RawTerm.rename_pointwise`. -/

theorem RawTerm.rename_identity {scope : Nat} :
    ∀ (term : RawTerm scope), term.rename RawRenaming.identity = term
  | .var _ => rfl
  | .unit => rfl
  | .lam body => by
      show (body.rename (@RawRenaming.identity scope).lift).lam = body.lam
      rw [RawTerm.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) body,
          RawTerm.rename_identity body]
  | .app fnTerm argTerm => by
      show (fnTerm.rename _).app (argTerm.rename _) = (fnTerm.app argTerm)
      rw [RawTerm.rename_identity fnTerm, RawTerm.rename_identity argTerm]
  | .pair firstTerm secondTerm => by
      show (firstTerm.rename _).pair (secondTerm.rename _) = (firstTerm.pair secondTerm)
      rw [RawTerm.rename_identity firstTerm, RawTerm.rename_identity secondTerm]
  | .fst pairTerm => by
      show (pairTerm.rename _).fst = pairTerm.fst
      rw [RawTerm.rename_identity pairTerm]
  | .snd pairTerm => by
      show (pairTerm.rename _).snd = pairTerm.snd
      rw [RawTerm.rename_identity pairTerm]
  | .boolTrue => rfl
  | .boolFalse => rfl
  | .boolElim scrutinee thenBranch elseBranch => by
      show (scrutinee.rename _).boolElim (thenBranch.rename _) (elseBranch.rename _) =
           scrutinee.boolElim thenBranch elseBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity thenBranch,
          RawTerm.rename_identity elseBranch]
  | .natZero => rfl
  | .natSucc predecessor => by
      show (predecessor.rename _).natSucc = predecessor.natSucc
      rw [RawTerm.rename_identity predecessor]
  | .natElim scrutinee zeroBranch succBranch => by
      show (scrutinee.rename _).natElim (zeroBranch.rename _) (succBranch.rename _) =
           scrutinee.natElim zeroBranch succBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity zeroBranch,
          RawTerm.rename_identity succBranch]
  | .natRec scrutinee zeroBranch succBranch => by
      show (scrutinee.rename _).natRec (zeroBranch.rename _) (succBranch.rename _) =
           scrutinee.natRec zeroBranch succBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity zeroBranch,
          RawTerm.rename_identity succBranch]
  | .listNil => rfl
  | .listCons headTerm tailTerm => by
      show (headTerm.rename _).listCons (tailTerm.rename _) = headTerm.listCons tailTerm
      rw [RawTerm.rename_identity headTerm, RawTerm.rename_identity tailTerm]
  | .listElim scrutinee nilBranch consBranch => by
      show (scrutinee.rename _).listElim (nilBranch.rename _) (consBranch.rename _) =
           scrutinee.listElim nilBranch consBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity nilBranch,
          RawTerm.rename_identity consBranch]
  | .optionNone => rfl
  | .optionSome valueTerm => by
      show (valueTerm.rename _).optionSome = valueTerm.optionSome
      rw [RawTerm.rename_identity valueTerm]
  | .optionMatch scrutinee noneBranch someBranch => by
      show (scrutinee.rename _).optionMatch (noneBranch.rename _) (someBranch.rename _) =
           scrutinee.optionMatch noneBranch someBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity noneBranch,
          RawTerm.rename_identity someBranch]
  | .eitherInl valueTerm => by
      show (valueTerm.rename _).eitherInl = valueTerm.eitherInl
      rw [RawTerm.rename_identity valueTerm]
  | .eitherInr valueTerm => by
      show (valueTerm.rename _).eitherInr = valueTerm.eitherInr
      rw [RawTerm.rename_identity valueTerm]
  | .eitherMatch scrutinee leftBranch rightBranch => by
      show (scrutinee.rename _).eitherMatch (leftBranch.rename _) (rightBranch.rename _) =
           scrutinee.eitherMatch leftBranch rightBranch
      rw [RawTerm.rename_identity scrutinee,
          RawTerm.rename_identity leftBranch,
          RawTerm.rename_identity rightBranch]
  | .refl rawWitness => by
      show (rawWitness.rename _).refl = rawWitness.refl
      rw [RawTerm.rename_identity rawWitness]
  | .idJ baseRaw witnessRaw => by
      show (baseRaw.rename _).idJ (witnessRaw.rename _) = baseRaw.idJ witnessRaw
      rw [RawTerm.rename_identity baseRaw, RawTerm.rename_identity witnessRaw]
  | .modIntro innerTerm => by
      show (innerTerm.rename _).modIntro = innerTerm.modIntro
      rw [RawTerm.rename_identity innerTerm]
  | .modElim innerTerm => by
      show (innerTerm.rename _).modElim = innerTerm.modElim
      rw [RawTerm.rename_identity innerTerm]
  | .subsume innerTerm => by
      show (innerTerm.rename _).subsume = innerTerm.subsume
      rw [RawTerm.rename_identity innerTerm]

/-! ## Ty.rename_identity

Structural induction over Ty.  The `id` ctor's arms (left/right
endpoints) are RawTerms, so they reduce via `RawTerm.rename_identity`. -/

theorem Ty.rename_identity {level scope : Nat} :
    ∀ (someType : Ty level scope),
      someType.rename RawRenaming.identity = someType
  | .unit => rfl
  | .bool => rfl
  | .nat  => rfl
  | .arrow domainType codomainType => by
      show (domainType.rename _).arrow (codomainType.rename _) =
           domainType.arrow codomainType
      rw [Ty.rename_identity domainType, Ty.rename_identity codomainType]
  | .piTy domainType codomainType => by
      show (domainType.rename _).piTy (codomainType.rename _) =
           domainType.piTy codomainType
      rw [Ty.rename_identity domainType,
          Ty.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) codomainType,
          Ty.rename_identity codomainType]
  | .sigmaTy firstType secondType => by
      show (firstType.rename _).sigmaTy (secondType.rename _) =
           firstType.sigmaTy secondType
      rw [Ty.rename_identity firstType,
          Ty.rename_pointwise (@RawRenaming.identity_lift_pointwise scope) secondType,
          Ty.rename_identity secondType]
  | .tyVar _ => rfl
  | .id carrier leftEndpoint rightEndpoint => by
      show (carrier.rename _).id (leftEndpoint.rename _) (rightEndpoint.rename _) =
           carrier.id leftEndpoint rightEndpoint
      rw [Ty.rename_identity carrier,
          RawTerm.rename_identity leftEndpoint,
          RawTerm.rename_identity rightEndpoint]
  | .listType elementType => by
      show (elementType.rename _).listType = elementType.listType
      rw [Ty.rename_identity elementType]
  | .optionType elementType => by
      show (elementType.rename _).optionType = elementType.optionType
      rw [Ty.rename_identity elementType]
  | .eitherType leftType rightType => by
      show (leftType.rename _).eitherType (rightType.rename _) =
           leftType.eitherType rightType
      rw [Ty.rename_identity leftType, Ty.rename_identity rightType]

end LeanFX2
