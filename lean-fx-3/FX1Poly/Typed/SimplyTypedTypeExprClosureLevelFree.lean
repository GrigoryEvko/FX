import FX1Poly.Typed.SimplyTypedTypeExprReducibleLevelFree
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.HasTypeDescPiWeakening

/-! # FX1Poly/Typed/SimplyTypedTypeExprClosureLevelFree
    — reducible type expressions are closed under renaming and substitution.

`IsReducibleTypeExprLF` carves out the simply-typed type expressions: universe-code leaves and arrows
(`piTyCodeCell domainCode (weaken codomainBase)`) of reducible type expressions.  The leaves are
variable-free (`universeCodeCell` is renaming- and substitution-invariant), so the whole class is structural:
applying any renaming or substitution to a reducible type expression yields another reducible type
expression of the same shape.

* `IsReducibleTypeExprLF.subst` — `IsReducibleTypeExprLF t → IsReducibleTypeExprLF (RawTerm.subst σ t)`.
* `IsReducibleTypeExprLF.rename` — `IsReducibleTypeExprLF t → IsReducibleTypeExprLF (RawTerm.rename ρ t)`.

(These are CLOSURE, not invariance: `subst σ t` lands at the substitution's target scope, so it is a genuinely
different term from `t` — only its membership in the reducible class is preserved.  The `arrow` arm threads
the `*_lift_weaken_commute` commutation through the codomain so the result re-presents as
`piTyCodeCell _ (weaken _)`, the shape the `arrow` constructor demands.)

These feed the subject-reduction arc: the `lam` rule of `SimplyTypedTermLF` carries `IsReducibleTypeExprLF`
premises on its domain and codomain, and the (downstream) renaming- and substitution-preservation lemmas must
transport exactly those premises across the renaming/substitution — which is what these closure lemmas
supply.

## Zero-axiom verification

Each is an induction on `IsReducibleTypeExprLF` whose `arrow` arm mirrors the existing semantic-reducibility
proof in `SimplyTypedTypeExprReducibleLevelFree`: `{subst,rename}_piTyCodeCell` to expose the renamed/
substituted Π, then `{subst,rename}_lift_weaken_commute` to pull the lift back through the weakened codomain.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per
declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Reducible type expressions are closed under substitution.**  A universe-code substitutes to itself; an
arrow `Π dom. weaken cod` substitutes to `Π (subst σ dom). weaken (subst σ cod)` (the lift pulled back through
the weakened codomain by `subst_lift_weaken_commute`), still an arrow of reducible type expressions. -/
theorem IsReducibleTypeExprLF.subst {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    {typeExpr : RawTerm scope} (reducible : IsReducibleTypeExprLF typeExpr) :
    IsReducibleTypeExprLF (RawTerm.subst sigma typeExpr) := by
  induction reducible with
  | universeCode levelExpr flag =>
      rw [subst_universeCodeCell]
      exact .universeCode levelExpr flag
  | arrow _domainExpr _codomainExpr ihDomain ihCodomain =>
      rename_i domainCode codomainBase
      have typeEq : RawTerm.subst sigma (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
          = piTyCodeCell (RawTerm.subst sigma domainCode)
              (RawTerm.weaken (RawTerm.subst sigma codomainBase)) := by
        rw [subst_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.subst sigma domainCode))
          (subst_lift_weaken_commute sigma codomainBase)
      rw [typeEq]
      exact .arrow ihDomain ihCodomain

/-- **Reducible type expressions are closed under renaming.**  Mirror of `subst`: a universe-code renames to
itself; an arrow renames component-wise, the lift pulled back through the weakened codomain by
`rename_lift_weaken_commute`. -/
theorem IsReducibleTypeExprLF.rename {sourceScope targetScope : Nat}
    (rawRenaming : Foundation.RawRenaming sourceScope targetScope)
    {typeExpr : RawTerm sourceScope} (reducible : IsReducibleTypeExprLF typeExpr) :
    IsReducibleTypeExprLF (RawTerm.rename rawRenaming typeExpr) := by
  induction reducible with
  | universeCode levelExpr flag =>
      rw [rename_universeCodeCell]
      exact .universeCode levelExpr flag
  | arrow _domainExpr _codomainExpr ihDomain ihCodomain =>
      rename_i domainCode codomainBase
      have typeEq : RawTerm.rename rawRenaming (piTyCodeCell domainCode (RawTerm.weaken codomainBase))
          = piTyCodeCell (RawTerm.rename rawRenaming domainCode)
              (RawTerm.weaken (RawTerm.rename rawRenaming codomainBase)) := by
        rw [rename_piTyCodeCell]
        exact congrArg (piTyCodeCell (RawTerm.rename rawRenaming domainCode))
          (rename_lift_weaken_commute rawRenaming codomainBase)
      rw [typeEq]
      exact .arrow ihDomain ihCodomain

end FX1Poly.Typed
