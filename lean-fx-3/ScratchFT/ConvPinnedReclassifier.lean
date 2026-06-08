import FX1Poly.Typed.LevelingBridge

/-! Scratch: the conv arm with a PINNED (type-variable) reclassifier — the case that walled the refined-motive
totalBridge. `typeVariableNotLevelFlexible` shows a type variable can't be ValidTyping-level-flexible, so the
refined motive's conjunct-2 (flexibility for all universe-classified subjects) is unsatisfiable for it. But the
conv rule does NOT need flexibility — it needs the reclassifier at exactly `subjectLevel + 1`, and a type variable
`var i : Type@e` IS valid there (at its PINNED level `contextLevels i`) PROVIDED the leveling is consistent:
`contextLevels i = subjectLevel + 1`. That equation holds by the leveling discipline (a type variable sits one
universe level above the subject it classifies). So the type-variable conv case is dischargeable — the blockage
was the over-demanding motive, not a real obstruction. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem validTypingBridgeConvPinnedReclassifier {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (subjectLevel : Nat)
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {index : Fin scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectTyped : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (converts : Conv classifier (variableCell index))
    (reclassifierIsUniverse : context.lookup index = universeCodeCell levelExpr flag)
    (levelMatch : contextLevels index = subjectLevel + 1) :
    ValidTyping profile contextLevels subjectLevel context subject (variableCell index) := by
  apply ValidTyping.conv contextLevels subjectLevel subjectTyped converts
  rw [← levelMatch, ← reclassifierIsUniverse]
  exact ValidTyping.var contextLevels context index

end FX1Poly.Typed

#print axioms FX1Poly.Typed.validTypingBridgeConvPinnedReclassifier
