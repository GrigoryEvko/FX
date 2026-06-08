import FX1Poly.Typed.FormationCanonicalForms

/-! Scratch: formation-engine consistency via the recursor + Lemma A (no reconstruction). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem HasTypeDesc.noClosedFormationTermAtEmptyType {profile : PolyProfile} {subject : RawTerm 0}
    (typed : HasTypeDesc profile (TypingContext.empty : TypingContext profile 0) subject
      (emptyTypeCell (scope := 0))) :
    False := by
  refine (HasTypeDesc.rec
    (motive_1 := fun {scope} _context _subject classifier _typed =>
      RawTerm.headGenerator classifier = Generator.gen_emptyCode → (Fin scope → False) → False)
    (motive_2 := fun _context _levels _flag _children _telescope => True)
    ?var ?conv ?universeFormation ?genFormation ?nilTelescope ?consTelescope typed)
    rfl (fun emptyIndex => emptyIndex.elim0)
  · -- var: the looked-up classifier; the closed hypothesis kills the index
    intro _scope _context index _headEq closed
    exact closed index
  · -- conv: the reclassifier is closed-typed at a universe code, so by Lemma A its head is a former /
    -- universe — contradicting headEq (gen_emptyCode)
    intro _scope _context _subject _classifier _reclassifier _levelExpr _flag _typed _converts
      reclassifierTyped _subjectIH _reclassifierIH headEq closed
    rcases HasTypeDesc.subjectIsVariableOrFormerHead reclassifierTyped with ⟨index, _⟩ | headIsFormer
    · exact closed index
    · rcases headIsFormer with isPi | isSigma | isUniverse
      · exact Generator.noConfusion (headEq ▸ isPi)
      · exact Generator.noConfusion (headEq ▸ isSigma)
      · exact Generator.noConfusion (headEq ▸ isUniverse)
  · -- universeFormation: classifier is a universe code, head ≠ gen_emptyCode
    intro _scope _context _levelExpr _flag headEq _closed
    exact Generator.noConfusion headEq
  · -- genFormation: classifier is universeFormerOutput = a universe code, head ≠ gen_emptyCode
    intro _scope _context generator _payload _children levels flag rule isFormation _premises
      _premisesIH headEq _closed
    rw [typingRuleDescOf_outputIsUniverseFormer isFormation] at headEq
    exact Generator.noConfusion headEq
  · intro _baseScope _currentDepth _context _flag
    exact True.intro
  · intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped _headIH _restIH
    exact True.intro

#print axioms FX1Poly.Typed.HasTypeDesc.noClosedFormationTermAtEmptyType

end FX1Poly.Typed
