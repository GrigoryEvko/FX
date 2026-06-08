import FX1Poly.Typed.ValidTypingLevelFlexible
import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.LevelingBridge

/-! Scratch probe (step 1 of the SN-43 totalBridge): the formation sub-bridge `HasTypeDesc → ValidTyping`.
Goal: get var + universeFormation arms clean (no hypothesis), and READ OFF the exact conv + genFormation goals
so I know precisely what leveling the conv arm needs and what telescope the genFormation arm needs. Bare
`contextLevels` parameter (no LeveledContext yet) — I want to see the raw obligations first. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

set_option maxHeartbeats 1000000 in
theorem formationBridgeProbe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (contextLevels : Fin scope → Nat)
    {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    ∃ subjectLevel : Nat, ValidTyping profile contextLevels subjectLevel context subject classifier := by
  induction typed with
  | var context index =>
      exact ⟨_, ValidTyping.var contextLevels context index⟩
  | universeFormation context levelExpr flag =>
      exact ⟨_, ValidTyping.universeFormation contextLevels 0 context levelExpr flag⟩
  | conv levelExpr flag typed converts reclassifierTyped subjectIH reclassifierIH =>
      sorry
  | genFormation context generator payload children levels flag rule isFormation premises =>
      sorry

end FX1Poly.Typed
