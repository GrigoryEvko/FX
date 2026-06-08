import FX1Poly.Typed.ValidTypingRefinedMotive

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- The revised-motive term wrapper: a subject valid at one level whose classifier is NOT convertible to any
universe code satisfies the revised motive (conjunct-2 vacuous — its convertibility guard is unsatisfiable). The
binder/elim term-output arms consume this with `Conv.piTyCode_not_universeCode` etc. -/
theorem RevisedBridgeConclusion.ofTermValidity {profile : PolyProfile} {scope : Nat}
    {contextLevels : Fin scope → Nat} {subjectLevel : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : ValidTyping profile contextLevels subjectLevel context subject classifier)
    (classifierNotConvUniverse : ∀ (levelExpr : LevelExpr) (flag : UniverseFlag),
      ¬ Conv classifier (universeCodeCell levelExpr flag)) :
    RevisedBridgeConclusion profile contextLevels context subject classifier :=
  ⟨⟨subjectLevel, typed⟩,
   fun levelExpr flag classifierConv _subjectNotVariable =>
     absurd classifierConv (classifierNotConvUniverse levelExpr flag)⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.RevisedBridgeConclusion.ofTermValidity
