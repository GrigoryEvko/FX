import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree

/-! # FX1Poly/Typed/SimplyTypedTermInhabitationLevelFree
    — concrete inhabitants of the simply-typed term judgment (the fundamental theorem is non-vacuous)

The simply-typed term fundamental theorem (`SimplyTypedTermFundamentalLevelFree`) and its strong-normalization
corollary are only meaningful if the judgment `SimplyTypedTermLF` is INHABITED.  This file ships concrete
witnesses: the polymorphic identity at a universe base type and at an arrow type, each a genuine
`SimplyTypedTermLF` derivation, with their strong normalization as fundamental-theorem corollaries.  This is
the simply-typed analogue of the typed-honesty corpus (`TY-honesty`): it confirms the metatheory applies to
real terms rather than being vacuously true.

  * `identityIsSimplyTyped` — `λx:Type@0. x : Type@0 → Type@0` (the `lam` rule over a universe-code domain;
    body via the `var` rule, whose looked-up type `(context.cons D).lookup ⟨0,_⟩` is the weakened binding by
    `TypingContext.lookup_cons_zero`).
  * `arrowIdentityIsSimplyTyped` — `λx:(Type@0→Type@0). x : (Type@0→Type@0) → (Type@0→Type@0)`, the same
    identity term at an ARROW type, exercising the `IsReducibleTypeExprLF.arrow` case of the domain supplier.
  * `identityStronglyNormalizing` / `arrowIdentityStronglyNormalizing` — strong normalization of the (closed)
    identity under any substitution into a non-empty scope, by `SimplyTypedTermLF.stronglyNormalizingClosed`.

The bound variable is written `⟨0, Nat.zero_lt_succ 0⟩`, NOT the `(0 : Fin 1)` `OfNat` numeral, which would
leak `propext` / `Quot.sound` through `Fin`'s decidable machinery.

## Zero-axiom verification

`apply SimplyTypedTermLF.lam` with the type-expression witnesses, then `rwa [TypingContext.lookup_cons_zero]`
to reconcile the `var` rule's looked-up type with the lambda's weakened codomain (the `RawTerm.weaken` /
`rename RawRenaming.weaken` definitional unfolding rides through `assumption`).  The corollaries are
`stronglyNormalizingClosed` projections.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- `Type@0` (standard flag) as a closed base type at any scope. -/
def typeZeroCode (scope : Nat) : RawTerm scope :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The simple arrow `Type@0 → Type@0` as a closed type at any scope. -/
def arrowTypeZeroCode (scope : Nat) : RawTerm scope :=
  piTyCodeCell (typeZeroCode scope) (RawTerm.weaken (typeZeroCode scope))

/-- **The polymorphic identity is a simply-typed term.**  `λx:Type@0. x : Type@0 → Type@0` is a genuine
`SimplyTypedTermLF` derivation — the `lam` rule over a universe-code domain, its body the `var` rule (whose
looked-up type is the weakened binding, `TypingContext.lookup_cons_zero`). -/
theorem identityIsSimplyTyped {profile : PolyProfile} :
    SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0)
      (lamCell (variableCell ⟨0, Nat.zero_lt_succ 0⟩))
      (piTyCodeCell (typeZeroCode 0) (RawTerm.weaken (typeZeroCode 0))) := by
  apply SimplyTypedTermLF.lam
    (IsReducibleTypeExprLF.universeCode LevelExpr.lzero UniverseFlag.standard)
    (IsReducibleTypeExprLF.universeCode LevelExpr.lzero UniverseFlag.standard)
  have varDeriv := SimplyTypedTermLF.var
    (context := (TypingContext.empty : TypingContext profile 0).cons
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) ⟨0, Nat.zero_lt_succ 0⟩
  rwa [TypingContext.lookup_cons_zero] at varDeriv

/-- **Strong normalization of the identity.**  The identity, closed by any substitution into a non-empty
scope, strongly normalizes — the fundamental theorem's strong-normalization corollary on a concrete
inhabitant. -/
theorem identityStronglyNormalizing {profile : PolyProfile} {targetScope : Nat}
    (substitution : RawTermSubst 0 (targetScope + 1)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution (lamCell (variableCell ⟨0, Nat.zero_lt_succ 0⟩))) :=
  (identityIsSimplyTyped (profile := profile)).stronglyNormalizingClosed substitution

/-- **The identity at an arrow type is a simply-typed term.**  `λx:(Type@0→Type@0). x :
(Type@0→Type@0) → (Type@0→Type@0)` — the same identity term at an ARROW type, exercising the
`IsReducibleTypeExprLF.arrow` case of the domain supplier. -/
theorem arrowIdentityIsSimplyTyped {profile : PolyProfile} :
    SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0)
      (lamCell (variableCell ⟨0, Nat.zero_lt_succ 0⟩))
      (piTyCodeCell (arrowTypeZeroCode 0) (RawTerm.weaken (arrowTypeZeroCode 0))) := by
  apply SimplyTypedTermLF.lam
    (IsReducibleTypeExprLF.arrow
      (IsReducibleTypeExprLF.universeCode LevelExpr.lzero UniverseFlag.standard)
      (IsReducibleTypeExprLF.universeCode LevelExpr.lzero UniverseFlag.standard))
    (IsReducibleTypeExprLF.arrow
      (IsReducibleTypeExprLF.universeCode LevelExpr.lzero UniverseFlag.standard)
      (IsReducibleTypeExprLF.universeCode LevelExpr.lzero UniverseFlag.standard))
  have varDeriv := SimplyTypedTermLF.var
    (context := (TypingContext.empty : TypingContext profile 0).cons (arrowTypeZeroCode 0))
    ⟨0, Nat.zero_lt_succ 0⟩
  rwa [TypingContext.lookup_cons_zero] at varDeriv

/-- **Strong normalization of the arrow-typed identity.** -/
theorem arrowIdentityStronglyNormalizing {profile : PolyProfile} {targetScope : Nat}
    (substitution : RawTermSubst 0 (targetScope + 1)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution (lamCell (variableCell ⟨0, Nat.zero_lt_succ 0⟩))) :=
  (arrowIdentityIsSimplyTyped (profile := profile)).stronglyNormalizingClosed substitution

end FX1Poly.Typed
