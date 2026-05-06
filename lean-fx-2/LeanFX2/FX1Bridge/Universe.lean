import LeanFX2.Term
import LeanFX2.FX1.Core.HasType
import LeanFX2.FX1Bridge.RoundTrip

/-! # FX1Bridge/Universe

Root status: Bridge.

Same-level universe-code bridge fragment.  Unlike the staged Bool/Nat
fragments, this maps rich universe codes to native FX1 sorts:

* rich `RawTerm.universeCode level.toNat` encodes as `FX1.Expr.sort level`
* rich `Ty.universe level` encodes as the successor FX1 sort

This file intentionally handles only the same-level case.  Rich cumulativity
allows an inner universe code to inhabit a higher outer universe, but FX1/Core
does not yet have universe-level cumulativity in `DefEq`, so the bridge does
not claim that cross-level fragment.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Encode finite rich universe levels into the matching FX1 level syntax. -/
def encodeUniverseLevel : UniverseLevel -> FX1.Level
  | UniverseLevel.zero => FX1.Level.zero
  | UniverseLevel.succ lowerLevel =>
      FX1.Level.succ (encodeUniverseLevel lowerLevel)
  | UniverseLevel.max leftLevel rightLevel =>
      FX1.Level.max
        (encodeUniverseLevel leftLevel)
        (encodeUniverseLevel rightLevel)
  | UniverseLevel.imax leftLevel rightLevel =>
      FX1.Level.imax
        (encodeUniverseLevel leftLevel)
        (encodeUniverseLevel rightLevel)

/-- Rich raw universe code at the same inner and outer universe level. -/
def universeCodeSameLevelRaw (universeLevel : UniverseLevel) : RawTerm 0 :=
  RawTerm.universeCode universeLevel.toNat

/-- FX1 encoding of a rich same-level universe code term. -/
def encodeRawTerm_universeCodeSameLevel
    (universeLevel : UniverseLevel) : FX1.Expr :=
  FX1.Expr.sort (encodeUniverseLevel universeLevel)

/-- FX1 encoding of the rich universe type inhabited by a same-level universe
code. -/
def encodeTy_universeSameLevel
    (universeLevel : UniverseLevel) : FX1.Expr :=
  FX1.Expr.sort (FX1.Level.succ (encodeUniverseLevel universeLevel))

/-- The FX1 level encoder is structurally reflexive under FX1's native
Boolean equality. -/
theorem encodeUniverseLevel_beq_self
    (universeLevel : UniverseLevel) :
    Eq
      (FX1.Level.beq
        (encodeUniverseLevel universeLevel)
        (encodeUniverseLevel universeLevel))
      true :=
  by
    induction universeLevel with
    | zero => rfl
    | succ lowerLevel lowerLevelBeqSelf =>
        exact lowerLevelBeqSelf
    | max leftLevel rightLevel leftLevelBeqSelf rightLevelBeqSelf =>
        change
          Bool.and
            (FX1.Level.beq
              (encodeUniverseLevel leftLevel)
              (encodeUniverseLevel leftLevel))
            (FX1.Level.beq
              (encodeUniverseLevel rightLevel)
              (encodeUniverseLevel rightLevel)) =
          true
        rw [leftLevelBeqSelf, rightLevelBeqSelf]
        exact Eq.refl true
    | imax leftLevel rightLevel leftLevelBeqSelf rightLevelBeqSelf =>
        change
          Bool.and
            (FX1.Level.beq
              (encodeUniverseLevel leftLevel)
              (encodeUniverseLevel leftLevel))
            (FX1.Level.beq
              (encodeUniverseLevel rightLevel)
              (encodeUniverseLevel rightLevel)) =
          true
        rw [leftLevelBeqSelf, rightLevelBeqSelf]
        exact Eq.refl true

/-- Fragment decoder for the rich universe type encoded at its same FX1
level.  The rich ambient level remains explicit because FX1/Core does not yet
represent rich cumulativity in its conversion relation. -/
def decodeTy_universeSameLevel
    {ambientLevel : Nat}
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 <= ambientLevel) :
    FX1.Expr -> Option (Ty ambientLevel 0)
  | FX1.Expr.sort (FX1.Level.succ actualLevel) =>
      match FX1.Level.beq actualLevel (encodeUniverseLevel universeLevel) with
      | true => Option.some (Ty.universe universeLevel levelLe)
      | false => Option.none
  | FX1.Expr.sort FX1.Level.zero => Option.none
  | FX1.Expr.sort (FX1.Level.max _ _) => Option.none
  | FX1.Expr.sort (FX1.Level.imax _ _) => Option.none
  | FX1.Expr.sort (FX1.Level.param _) => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none
  | FX1.Expr.app _ _ => Option.none

/-- Fragment decoder for the rich same-level universe-code raw term. -/
def decodeRawTerm_universeCodeSameLevel
    (universeLevel : UniverseLevel) :
    FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.sort actualLevel =>
      match FX1.Level.beq actualLevel (encodeUniverseLevel universeLevel) with
      | true => Option.some (universeCodeSameLevelRaw universeLevel)
      | false => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none
  | FX1.Expr.app _ _ => Option.none

/-- Decoding the exact same-level universe type encoding reconstructs the
rich universe type for the caller's ambient level. -/
theorem decodeTy_universeSameLevel_encode
    {ambientLevel : Nat}
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 <= ambientLevel) :
    Eq
      (decodeTy_universeSameLevel universeLevel levelLe
        (encodeTy_universeSameLevel universeLevel))
      (Option.some (Ty.universe universeLevel levelLe)) :=
  by
    change
      (match
        FX1.Level.beq
          (encodeUniverseLevel universeLevel)
          (encodeUniverseLevel universeLevel)
      with
      | true => Option.some (Ty.universe universeLevel levelLe)
      | false => Option.none) =
      Option.some (Ty.universe universeLevel levelLe)
    rw [encodeUniverseLevel_beq_self universeLevel]

/-- Decoding the exact same-level universe-code raw encoding reconstructs the
rich universe-code raw term. -/
theorem decodeRawTerm_universeCodeSameLevel_encode
    (universeLevel : UniverseLevel) :
    Eq
      (decodeRawTerm_universeCodeSameLevel universeLevel
        (encodeRawTerm_universeCodeSameLevel universeLevel))
      (Option.some (universeCodeSameLevelRaw universeLevel)) :=
  by
    change
      (match
        FX1.Level.beq
          (encodeUniverseLevel universeLevel)
          (encodeUniverseLevel universeLevel)
      with
      | true => Option.some (universeCodeSameLevelRaw universeLevel)
      | false => Option.none) =
      Option.some (universeCodeSameLevelRaw universeLevel)
    rw [encodeUniverseLevel_beq_self universeLevel]

/-- Same-level universe-code encoding computes to the native FX1 sort. -/
theorem encodeRawTerm_universeCodeSameLevel_eq_sort
    (universeLevel : UniverseLevel) :
    Eq
      (encodeRawTerm_universeCodeSameLevel universeLevel)
      (FX1.Expr.sort (encodeUniverseLevel universeLevel)) :=
  Eq.refl (FX1.Expr.sort (encodeUniverseLevel universeLevel))

/-- Same-level universe-type encoding computes to the successor FX1 sort. -/
theorem encodeTy_universeSameLevel_eq_successor_sort
    (universeLevel : UniverseLevel) :
    Eq
      (encodeTy_universeSameLevel universeLevel)
      (FX1.Expr.sort
        (FX1.Level.succ (encodeUniverseLevel universeLevel))) :=
  Eq.refl
    (FX1.Expr.sort
      (FX1.Level.succ (encodeUniverseLevel universeLevel)))

/-- Canonical rich term for a universe code inhabiting its own universe level.

The ambient rich level is still explicit because `Ty.universe` is cumulative at
the rich layer: a code for universe `level` may be placed in any ambient level
that is at least its successor. -/
def universeCodeSameLevelTerm
    {mode : Mode}
    {ambientLevel : Nat}
    (universeLevel : UniverseLevel)
    (levelLe : universeLevel.toNat + 1 <= ambientLevel) :
    Term
      (Ctx.empty mode ambientLevel)
      (Ty.universe universeLevel levelLe)
      (universeCodeSameLevelRaw universeLevel) :=
  Term.universeCode
    universeLevel
    universeLevel
    (Nat.le_refl universeLevel.toNat)
    levelLe

/-- FX1 typing derivation for the encoded same-level universe code. -/
theorem encodedUniverseCodeSameLevel_has_type
    (universeLevel : UniverseLevel) :
    FX1.HasType
      FX1.Environment.empty
      FX1.Context.empty
      (encodeRawTerm_universeCodeSameLevel universeLevel)
      (encodeTy_universeSameLevel universeLevel) :=
  FX1.HasType.sort
    FX1.Context.empty
    (encodeUniverseLevel universeLevel)

/-- Soundness of the same-level universe-code bridge fragment.

The theorem is intentionally exact-fragment: the rich term must be a universe
code whose inner and outer level coincide.  Cross-level rich cumulativity is
left out until FX1/Core exposes a matching universe-cumulativity conversion. -/
theorem encodeTermSound_universeCodeSameLevel
    {mode : Mode}
    {ambientLevel : Nat}
    (universeLevel : UniverseLevel)
    {levelLe : universeLevel.toNat + 1 <= ambientLevel}
    (_codeTerm :
      Term
        (Ctx.empty mode ambientLevel)
        (Ty.universe universeLevel levelLe)
        (universeCodeSameLevelRaw universeLevel)) :
    FX1.HasType
      FX1.Environment.empty
      FX1.Context.empty
      (encodeRawTerm_universeCodeSameLevel universeLevel)
      (encodeTy_universeSameLevel universeLevel) :=
  encodedUniverseCodeSameLevel_has_type universeLevel

/-- Exact round-trip evidence for the same-level universe-code bridge
fragment. -/
def encodeTermSound_universeCodeSameLevel_roundTrip
    {mode : Mode}
    {ambientLevel : Nat}
    (universeLevel : UniverseLevel)
    {levelLe : universeLevel.toNat + 1 <= ambientLevel}
    (_codeTerm :
      Term
        (Ctx.empty mode ambientLevel)
        (Ty.universe universeLevel levelLe)
        (universeCodeSameLevelRaw universeLevel)) :
    BridgeRoundTrip
      (encodeTy_universeSameLevel universeLevel)
      (decodeTy_universeSameLevel universeLevel levelLe)
      (Ty.universe universeLevel levelLe)
      (encodeRawTerm_universeCodeSameLevel universeLevel)
      (decodeRawTerm_universeCodeSameLevel universeLevel)
      (universeCodeSameLevelRaw universeLevel) :=
  {
    typeRoundTrip :=
      decodeTy_universeSameLevel_encode universeLevel levelLe
    rawRoundTrip :=
      decodeRawTerm_universeCodeSameLevel_encode universeLevel
  }

end FX1Bridge
end LeanFX2
