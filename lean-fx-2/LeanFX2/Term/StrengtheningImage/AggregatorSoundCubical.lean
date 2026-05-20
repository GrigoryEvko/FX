import LeanFX2.Term.StrengtheningImage.AggregatorSoundCore

/-! # Term/StrengtheningImage/AggregatorSoundCubical

Aggregator-soundness instances for cubical homogeneous composition wrappers.
-/

namespace LeanFX2

namespace Term

/-- Aggregator wrapper at the `Term.hcomp` arm.  Cubical homogeneous
composition: two flat-context value IHs (sides + cap); the
`modeIsUnivalent` discipline witness threads through unstrengthened. -/
theorem isAggregatorSound_hcomp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    {sidesValue : Term sourceCtx carrierType sidesRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesAggregator : IsAggregatorSound sidesValue)
    (capAggregator : IsAggregatorSound capValue) :
    IsAggregatorSound
      (Term.hcomp (context := sourceCtx) (carrierType := carrierType)
        (sidesRaw := sidesRaw) (capRaw := capRaw) modeIsUnivalent
        sidesValue capValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atHcomp_imp_sound modeIsUnivalent
    strengthening
    (sidesAggregator strengthening)
    (capAggregator strengthening)
    result success

/-- Aggregator wrapper at the `Term.hcompPath` arm.  Path-shaped cubical
composition: two flat-context value IHs (sidesPath + cap); positional
`leftEndpoint`/`rightEndpoint` (raw endpoints) thread through, internal
Ty-witness splits for carrier + endpoints handled by the leaf. -/
theorem isAggregatorSound_hcompPath {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    {sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term sourceCtx carrierType capRaw}
    (sidesAggregator : IsAggregatorSound sidesPath)
    (capAggregator : IsAggregatorSound capValue) :
    IsAggregatorSound
      (Term.hcompPath (context := sourceCtx) (carrierType := carrierType)
        (sidesPathRaw := sidesPathRaw) (capRaw := capRaw)
        modeIsUnivalent leftEndpoint rightEndpoint sidesPath capValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atHcompPath_imp_sound modeIsUnivalent
    leftEndpoint rightEndpoint strengthening
    (sidesAggregator strengthening)
    (capAggregator strengthening)
    result success

end Term

end LeanFX2
