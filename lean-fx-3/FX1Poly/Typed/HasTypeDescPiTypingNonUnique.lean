import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.ConvCodeInjectivity
import FX1Poly.Typed.HasTypeDecidableConv

/-! # FX1Poly/Typed/HasTypeDescPiTypingNonUnique
    — the grown engine's typing is NON-UNIQUE for a bare Curry-style λ (the SN-052 design fact)

`HasTypeDescPi.piIntro` types a BARE abstraction `lamCell body` — the `lamCell` carries NO domain
annotation (the domain `domainCode` is a separate premise, not part of the subject term).  So the SAME
closed identity λ `lamCell (var 0)` inhabits `Π (Type@e) (Type@e)` for EVERY level `e`, and distinct
levels give NON-convertible types.  Typing is therefore NOT unique up to `Conv` (unlike the formation
fragment, where `HasTypeDesc.uniqueness` holds).

## Why this matters: SN-052 must be BIDIRECTIONAL

Decidable typed CONVERSION (SN-051, `Conv.decidableOfWellTypedInWfContext`) is shipped unconditionally via
OB-5 strong normalization.  The natural route to decidable typed CHECKING (SN-052) — "synthesize the
term's unique type, then compare to the target via `Conv`" — is UNAVAILABLE here: there is no unique type to
synthesize at a λ.  The grown-engine checker must instead be BIDIRECTIONAL: at a λ it works in CHECK mode,
normalizing the GIVEN target to expose a `Π`-head (via SN + `Conv.piTyCode_inj`) and recursively checking the
body against the codomain.  This file is the concrete witness pinning that design constraint.

## Zero-axiom verification

The typing derivation is a direct `piIntro` (domain/codomain by `universeFormation`, body by `var`, all via
`ofFormation`); the non-`Conv` is `Conv.piTyCode_inj` + `levelFlag_eq_of_conv_universeCodeCell` +
`LevelExpr.noConfusion`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The closed identity λ is typeable at `Π (Type@e) (Type@e)` for EVERY level `e`.**  Built directly from
the grown `piIntro` arm: domain and codomain are the universe code `Type@e` (typed at `Type@(e+1)` by the
formation engine's `universeFormation`), and the body `var 0` is typed at the consed domain `Type@e` by the
`var` arm.  The level `e` is FREE — nothing in the subject `lamCell (var 0)` pins it. -/
theorem hasTypeDescPi_identityLambda_atUniverse {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
      (piTyCodeCell (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)) :=
  HasTypeDescPi.piIntro levelExpr.lsucc levelExpr.lsucc flag
    (.ofFormation (HasTypeDesc.universeFormation _ levelExpr flag))
    (.ofFormation (HasTypeDesc.universeFormation _ levelExpr flag))
    (.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- **Typing is NON-UNIQUE in the grown engine.**  The closed identity λ `lamCell (var 0)` inhabits two
NON-convertible Π types (`Π(Type@0)(Type@0)` and `Π(Type@1)(Type@1)`), because `lamCell` is a bare
Curry-style abstraction carrying no domain annotation.  Consequence: decidable typed CHECKING (SN-052) must be
BIDIRECTIONAL (CHECK mode at λ against the given target), NOT infer-then-compare — there is no unique type to
infer.  (Contrast the formation fragment, where `HasTypeDesc.uniqueness` DOES hold.) -/
theorem hasTypeDescPi_typing_notUnique {profile : PolyProfile} (flag : UniverseFlag) :
    ∃ (subject firstType secondType : RawTerm 0),
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject firstType ∧
      HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject secondType ∧
      ¬ Conv firstType secondType := by
  refine ⟨_, _, _,
    hasTypeDescPi_identityLambda_atUniverse LevelExpr.lzero flag,
    hasTypeDescPi_identityLambda_atUniverse LevelExpr.lzero.lsucc flag, ?_⟩
  intro piTypesConvert
  obtain ⟨domainConvert, _codomainConvert⟩ := Conv.piTyCode_inj piTypesConvert
  obtain ⟨levelsEqual, _flagsEqual⟩ :=
    levelFlag_eq_of_conv_universeCodeCell (context := (TypingContext.empty : TypingContext profile 0))
      domainConvert
  exact LevelExpr.noConfusion levelsEqual

end FX1Poly.Typed
