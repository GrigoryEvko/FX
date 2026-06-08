import FX1Poly.Typed.LevelingBridge

/-! Scratch v2: the LITERAL closed SN-043 milestone shape — `HasTypeDescPi .empty t T → SN t` — modulo the
empty-context leveling bridge (the natural closed-case form: a closed context's level vector IS `emptyLevelVector`).
Composes with the shipped, UNCONDITIONAL `ValidTyping.closedStronglyNormalizing` (which internally handles the
scope-0→scope-1 renaming reflection). No funext, no RawRenaming plumbing. This is the headline SN-043 statement
(SN-043/#546, SN-029/#532) with its one residual surfaced as the empty leveling bridge. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem hasTypeDescPiClosedStronglyNormalizingFromEmptyBridge {profile : PolyProfile}
    (emptyBridge :
      ∀ {subject classifier : RawTerm 0},
        HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier →
          ∃ predLevel : Nat,
            ValidTyping profile emptyLevelVector (predLevel + 1)
              (TypingContext.empty : TypingContext profile 0) subject classifier)
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsStronglyNormalizing subject := by
  obtain ⟨predLevel, validTyped⟩ := emptyBridge typed
  exact validTyped.closedStronglyNormalizing predLevel

end FX1Poly.Typed

#print axioms FX1Poly.Typed.hasTypeDescPiClosedStronglyNormalizingFromEmptyBridge
