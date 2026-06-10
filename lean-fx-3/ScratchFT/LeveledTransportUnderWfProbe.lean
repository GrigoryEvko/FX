import FX1Poly.Typed.TypedTypeValidityLeveledTransport
import FX1Poly.Typed.HasTypeDescPiContextConversionFlexibleUnderWf

/-! Probe: discharge the leveled transport's `neutralRecon` hypothesis under target well-formedness.

`HasTypeDescPi.convContextUnderWf` (SR-U5 era, unconditional under `WfContextDescPi target`) +
`convBackToUniverseCode` give the neutral arm's reconstruction outright — the `IsNeutral` premise is not
even needed.  Re-run the transport induction threading wf (extended at the `piType` binder exactly as
`convContextUnderWf`'s `piIntro` arm does) to get the wf-conditional leveled transport. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- A subject typed at an EXACT universe code survives pointwise-`Conv` context conversion at that same
exact universe code, given target well-formedness: `convContextUnderWf` lands it at a `Conv`-equal
classifier and `convBackToUniverseCode` pins the classifier back. -/
theorem HasTypeDescPi.universeClassifiedConvContextUnderWf {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {subject : RawTerm scope} {level : LevelExpr} {flag : UniverseFlag}
    (targetWf : WfContextDescPi targetContext)
    (typed : HasTypeDescPi profile sourceContext subject (universeCodeCell level flag))
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    HasTypeDescPi profile targetContext subject (universeCodeCell level flag) := by
  obtain ⟨reachedCode, universeConvToReached, typedAtReached⟩ :=
    HasTypeDescPi.convContextUnderWf typed targetContext targetWf contextConv
  exact typedAtReached.convBackToUniverseCode universeConvToReached

/-- The leveled transport with the neutral arm DISCHARGED: conditional only on target well-formedness. -/
theorem TypedTypeValidityLeveled.transportUnderWf {profile : PolyProfile}
    {scope : Nat} {sourceContext : TypingContext profile scope} {typeCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile sourceContext typeCode level flag box) :
    ∀ (targetContext : TypingContext profile scope),
      WfContextDescPi targetContext →
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      TypedTypeValidityLeveled profile targetContext typeCode level flag box := by
  induction relation with
  | neutral neutralCode validity =>
      intro targetContext targetWf contextConv
      exact TypedTypeValidityLeveled.neutral neutralCode
        (HasTypeDescPi.universeClassifiedConvContextUnderWf targetWf validity contextConv)
  | @universeType _armScope _armContext levelExpr armFlag _validity =>
      intro targetContext _targetWf _contextConv
      exact TypedTypeValidityLeveled.universeType
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation targetContext levelExpr armFlag))
  | @piType _armScope _armContext domainCode _codomainCode domainLevel codomainLevel armFlag
      _domainBox _codomainBox codomainFamily _domainValid _codomainValid _validity
      domainIH codomainIH =>
      intro targetContext targetWf contextConv
      have domainValid' := domainIH targetContext targetWf contextConv
      have extendedWf : WfContextDescPi (targetContext.cons domainCode) :=
        WfContextDescPi.cons targetWf ⟨domainLevel, armFlag, domainValid'.toHasTypeDescPi⟩
      have codomainValid' :=
        codomainIH (targetContext.cons domainCode) extendedWf
          (convContextCondition_cons domainCode contextConv)
      exact TypedTypeValidityLeveled.piType codomainFamily domainValid' codomainValid'
        (HasTypeDescPi.piFormationViaGenArm targetContext domainCode _codomainCode
          domainLevel codomainLevel armFlag
          domainValid'.toHasTypeDescPi codomainValid'.toHasTypeDescPi)

/-- The validity-transport payoff, wf-conditional: a leveled-valid type code's EXACT universe-code typing
transports across pointwise-`Conv` context conversion given target well-formedness. -/
theorem TypedTypeValidityLeveled.transportValidityUnderWf {profile : PolyProfile}
    {scope : Nat} {sourceContext targetContext : TypingContext profile scope}
    {typeCode : RawTerm scope} {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile sourceContext typeCode level flag box)
    (targetWf : WfContextDescPi targetContext)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    HasTypeDescPi profile targetContext typeCode (universeCodeCell level flag) :=
  (relation.transportUnderWf targetContext targetWf contextConv).toHasTypeDescPi

#print axioms FX1Poly.Typed.HasTypeDescPi.universeClassifiedConvContextUnderWf
#print axioms FX1Poly.Typed.TypedTypeValidityLeveled.transportUnderWf
#print axioms FX1Poly.Typed.TypedTypeValidityLeveled.transportValidityUnderWf

end FX1Poly.Typed
