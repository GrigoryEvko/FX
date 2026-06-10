import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.KripkeCandidateRenameClosure
import FX1Poly.Core.NeutralTerm

/-! Probe: the UNIVERSE-TRACKING refined typed type-validity LR (route B). Carries the universe (level, flag) in
    the INDEX, so the piType arm FORCES the domain and codomain to share the flag (resolving the flag-matching
    obstacle that blocked the unindexed TypedTypeValidityBoxed #1110 from rebuilding Π-validity via
    piFormationViaGenArm). Soundness `toHasTypeDescPi` is now UNIVERSE-PRESERVING (the exact universe code, not
    an existential). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The candidate box (mirrors `KripkeCandBox` from TypedTypeValidityBoxedRelation; redeclared here for the probe). -/
structure LeveledCandBox (scope : Nat) where
  run : KripkeCand scope

inductive TypedTypeValidityLeveled (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope →
      LevelExpr → UniverseFlag → LeveledCandBox scope → Prop where
  | neutral {scope : Nat} {context : TypingContext profile scope} {typeCode : RawTerm scope}
      {level : LevelExpr} {flag : UniverseFlag}
      (neutralCode : IsNeutral typeCode)
      (validity : HasTypeDescPi profile context typeCode (universeCodeCell level flag)) :
      TypedTypeValidityLeveled profile context typeCode level flag (LeveledCandBox.mk snKripkeCand)
  | universeType {scope : Nat} {context : TypingContext profile scope}
      {levelExpr : LevelExpr} {flag : UniverseFlag}
      (validity : HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)) :
      TypedTypeValidityLeveled profile context (universeCodeCell levelExpr flag)
        levelExpr.lsucc flag (LeveledCandBox.mk snKripkeCand)
  | piType {scope : Nat} {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
      {domainBox : LeveledCandBox scope} {codomainBox : LeveledCandBox (scope + 1)}
      (codomainFamily : KripkeCodFamily scope)
      (domainValid :
        TypedTypeValidityLeveled profile context domainCode domainLevel flag domainBox)
      (codomainValid :
        TypedTypeValidityLeveled profile (context.cons domainCode) codomainCode
          codomainLevel flag codomainBox)
      (validity : HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)) :
      TypedTypeValidityLeveled profile context (piTyCodeCell domainCode codomainCode)
        (LevelExpr.lmax domainLevel codomainLevel) flag
        (LeveledCandBox.mk (kripkeArrowDep domainBox.run codomainFamily))

/-- ★ UNIVERSE-PRESERVING soundness: the leveled relation carries the EXACT universe-code typing (not an
existential). This is the property the unindexed relation lacked — it makes the piType arm's domain and codomain
share the flag, so piFormationViaGenArm applies in the rebuild. -/
theorem TypedTypeValidityLeveled.toHasTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {box : LeveledCandBox scope}
    (relation : TypedTypeValidityLeveled profile context typeCode level flag box) :
    HasTypeDescPi profile context typeCode (universeCodeCell level flag) := by
  cases relation with
  | neutral _ validity => exact validity
  | universeType validity => exact validity
  | piType _ _ _ validity => exact validity

/-- Non-vacuity: the closed universe code is leveled-valid at `(levelExpr.lsucc, flag)`. -/
theorem smoke_closedUniverseLeveled {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    TypedTypeValidityLeveled (profile := profile)
      (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell levelExpr flag) levelExpr.lsucc flag (LeveledCandBox.mk snKripkeCand) :=
  TypedTypeValidityLeveled.universeType
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0) levelExpr flag))

end FX1Poly.Typed

#print axioms FX1Poly.Typed.TypedTypeValidityLeveled.toHasTypeDescPi
#print axioms FX1Poly.Typed.smoke_closedUniverseLeveled
