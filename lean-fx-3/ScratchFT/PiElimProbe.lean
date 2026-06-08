import FX1Poly.Typed.ValidTypingConvArm

/-! Probe: can the piElim arm of RevisedBridgeConclusion produce conjunct-1
    from the function/argument bridge IHs? The crux is the level-alignment:
    ValidTyping.piElim demands function and argument at the SAME subjectLevel,
    but the two bridge IHs supply INDEPENDENT existential levels.

    This probe tests whether the alignment is provable, needs a hypothesis,
    or needs a motive carrying a determined level. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

-- Attempt 1: naive — does the existential conjunct-1 align?
example {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionBridge : RevisedBridgeConclusion profile contextLevels context
      functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentBridge : RevisedBridgeConclusion profile contextLevels context
      argument domainCode) :
    ∃ subjectLevel : Nat,
      ValidTyping profile contextLevels subjectLevel context
        (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument) := by
  obtain ⟨⟨functionLevel, functionValid⟩, _⟩ := functionBridge
  obtain ⟨⟨argumentLevel, argumentValid⟩, _⟩ := argumentBridge
  -- Goal: align functionLevel and argumentLevel. Can we?
  refine ⟨functionLevel, ?_⟩
  -- ValidTyping.piElim needs argumentValid AT functionLevel, but it is at argumentLevel.
  sorry

end FX1Poly.Typed
