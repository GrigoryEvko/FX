import FX1Poly.Typed.LevelingBridge

/-! Scratch: SN-for-well-typed via the LIVE ValidTyping route, conditional ONLY on the leveling bridge
(totalBridge, #662) — NOT on the superseded fuel gate #672. Mirrors `hasTypeDescPiReducibleFromTotalBridge`
(which gives reducibility) but composes with the UNCONDITIONAL `ValidTyping.substStronglyNormalizing` to give SN
directly. This operationalizes the reframe: SN-043's only residual is the leveling bridge. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem hasTypeDescPiStronglyNormalizingFromTotalBridge {profile : PolyProfile}
    (totalBridge :
      ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
        HasTypeDescPi profile context subject classifier →
          ∃ (contextLevels : Fin scope → Nat) (predLevel : Nat),
            ValidTyping profile contextLevels (predLevel + 1) context subject classifier)
    {scope targetScope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    ∃ (contextLevels : Fin scope → Nat) (predLevel : Nat),
      ∀ (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvVec contextLevels context substitution →
          IsStronglyNormalizing (RawTerm.subst substitution subject) := by
  obtain ⟨contextLevels, predLevel, validTyped⟩ := totalBridge typed
  exact ⟨contextLevels, predLevel,
    fun substitution env => validTyped.substStronglyNormalizing predLevel substitution env⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.hasTypeDescPiStronglyNormalizingFromTotalBridge
