import FX1Poly.Typed.ValidTypingRefinedMotive

/-! Probe: the TotalBridgeConclusion.genFormationPi arm (canonical replacement
    for the deleted RefinedTotalBridgeConclusion.genFormationPi). The generic
    former is a TYPE CODE; its conjunct-2 refires ValidTyping.genFormationPi at
    each level and reclassifies through the convertibility guard via
    ValidTyping.conv (the old version used a syntactic `eq ▸`). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem TotalBridgeConclusion.genFormationPi {profile : PolyProfile} {scope : Nat}
    (contextLevels : Fin scope → Nat) (predLevel : Nat)
    {context : TypingContext profile scope}
    (generator : Generator) (payload : generator.payload scope)
    {children : RawTermChildren generator.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule)
    (premises : DescTelescopePi profile (currentDepth := 0) context levels flag children)
    (telescopeFundamental :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
        (_env : ReducibleEnvVec contextLevels context substitution)
        (shapeEq : generator.binderShifts = consecutiveShifts 0 levels.length),
        TelescopeReducible flag 0 levels.length substitution levels (shapeEq ▸ children)) :
    TotalBridgeConclusion profile contextLevels context
      (.mkGen generator payload children) (rule.outputType scope levels flag) :=
  ⟨⟨predLevel + 1,
    ValidTyping.genFormationPi contextLevels predLevel generator payload isFormation premises
      telescopeFundamental⟩,
   fun outLevel outFlag converts _subjectNotVariable level =>
     ValidTyping.conv contextLevels (level + 1)
       (ValidTyping.genFormationPi contextLevels level generator payload isFormation premises
         telescopeFundamental)
       converts
       (ValidTyping.universeFormation contextLevels (level + 1) context outLevel outFlag)⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.TotalBridgeConclusion.genFormationPi
