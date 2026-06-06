import FX1Poly.Typed.LevelingBridge

/-! # FX1Poly/Typed/ValidTypingLevelFlexible
    — level-flexible type codes: the refined-motive producers for the total bridge (SN-027, #656/#657)

The total bridge `HasTypeDescPi → ∃ contextLevels predLevel, ValidTyping …` (SN-027) cannot use the bare
`∃ subjectLevel` conclusion at the `conv` / `piElim` arms — those need their sub-derivations at a SHARED
`contextLevels` and at ALIGNED levels, which independent existentials do not force.  The resolution
(`LevelingBridge.lean`'s refined-motive note) is to give TYPE-CODE-classified subjects a `∀ level` conclusion:
they are LEVEL-FLEXIBLE, valid as a universe member at every positive level, because the formers
(`universeFormation` / `piFormation` / `sigmaFormation`) produce them at ANY `predLevel`.

This file ships that producer side: the `IsLevelFlexibleTypeCode` predicate and the three former arms that
build it, plus the connector showing a level-flexible reclassifier directly discharges the refined `conv`
bridge `validTypingBridgeConvFromAllLevelReclassifier`.  The `conv` arm of the refined motive lives in
`LevelingBridge.lean`; these are the level-flexible WITNESSES it consumes.

## What is proved

* `IsLevelFlexibleTypeCode` — a type code valid as a member of `Type@levelExpr[flag]` at every positive level.
* `universeFormation_isLevelFlexible` — `Type@e : Type@(lsucc e)` at every level (immediate: `predLevel` is
  free in `ValidTyping.universeFormation`).
* `piFormation_isLevelFlexible` / `sigmaFormation_isLevelFlexible` — a Π / Σ type code is level-flexible given
  an all-level domain (the shipped `∀ aboveLevel` premise) and a level-flexible codomain.
* `ValidTyping.convWithLevelFlexibleReclassifier` — the connector: a subject typed at one level, converting to
  a level-flexible reclassifier, is valid under that reclassifier (feeds the total-bridge `conv` arm).

## Zero-axiom verification

Each former arm is one application of the corresponding `ValidTyping` constructor under a `∀ level` lambda;
the connector is `validTypingBridgeConvFromAllLevelReclassifier`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- A type code is **level-flexible**: valid as a member of its universe `Type@levelExpr[flag]` at EVERY
positive level.  This is the refined-motive shape for type-code-classified subjects in the total bridge — the
shape the `conv` arm's `reclassifierAllLevel` premise consumes. -/
def IsLevelFlexibleTypeCode (profile : PolyProfile) {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (typeCode : RawTerm scope) (levelExpr : LevelExpr) (flag : UniverseFlag) : Prop :=
  ∀ level : Nat,
    ValidTyping profile contextLevels (level + 1) context typeCode (universeCodeCell levelExpr flag)

/-- **A universe code is level-flexible**: `Type@e : Type@(lsucc e)` at every level.  Immediate, because the
`ValidTyping.universeFormation` constructor's `predLevel` is a free parameter. -/
theorem universeFormation_isLevelFlexible {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsLevelFlexibleTypeCode profile contextLevels context
      (universeCodeCell levelExpr flag) levelExpr.lsucc flag :=
  fun level => ValidTyping.universeFormation contextLevels level context levelExpr flag

/-- **A Π type code is level-flexible** given an all-level domain and a level-flexible codomain.  At each
target level the Π former fires with `predLevel := level`, consuming the codomain at that same level. -/
theorem piFormation_isLevelFlexible {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : ∀ aboveLevel : Nat,
      ValidTyping profile contextLevels (aboveLevel + 1) context domainCode
        (universeCodeCell domainLevel flag))
    (codomainTyped : ∀ level headLevel : Nat,
      ValidTyping profile (levelCons headLevel contextLevels) (level + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    IsLevelFlexibleTypeCode profile contextLevels context
      (piTyCodeCell domainCode codomainCode) formerLevel flag :=
  fun level =>
    ValidTyping.piFormation contextLevels level domainTyped (fun headLevel => codomainTyped level headLevel)

/-- **A Σ type code is level-flexible** given an all-level domain and a level-flexible codomain. -/
theorem sigmaFormation_isLevelFlexible {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (context : TypingContext profile scope)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    (domainTyped : ∀ aboveLevel : Nat,
      ValidTyping profile contextLevels (aboveLevel + 1) context domainCode
        (universeCodeCell domainLevel flag))
    (codomainTyped : ∀ level : Nat,
      ValidTyping profile (levelCons (level + 1) contextLevels) (level + 1)
        (context.cons domainCode) codomainCode (universeCodeCell codomainLevel flag)) :
    IsLevelFlexibleTypeCode profile contextLevels context
      (sigmaTyCodeCell domainCode codomainCode) formerLevel flag :=
  fun level =>
    ValidTyping.sigmaFormation contextLevels level domainTyped (codomainTyped level)

/-- **Connector: a level-flexible reclassifier discharges the refined `conv` bridge.**  A subject typed at one
level, converting to a reclassifier that is a level-flexible type code, is valid under that reclassifier — this
is `validTypingBridgeConvFromAllLevelReclassifier` with the all-level premise supplied by
`IsLevelFlexibleTypeCode`.  It wires the former producers above into the total-bridge `conv` arm. -/
theorem ValidTyping.convWithLevelFlexibleReclassifier {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {subject classifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectTyped : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (converts : Conv classifier reclassifier)
    (reclassifierFlexible :
      IsLevelFlexibleTypeCode profile contextLevels context reclassifier levelExpr flag) :
    ∃ resultLevel : Nat,
      ValidTyping profile contextLevels resultLevel context subject reclassifier :=
  validTypingBridgeConvFromAllLevelReclassifier contextLevels subjectLevel
    subjectTyped converts reclassifierFlexible

end FX1Poly.Typed
