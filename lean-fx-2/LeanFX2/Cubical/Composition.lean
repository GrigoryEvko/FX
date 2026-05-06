import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.Cumul

/-! # Cubical/Composition

Homogeneous composition helpers for the current rich-layer cubical fragment.

Root status: FX-rich.

Bridge obligations:
* add the `RawTerm.hcomp` encoding case to `FX1.encodeRawTerm`;
* add the typed `Term.hcomp` encoding/soundness case once rich terms are
  bridged into FX1;
* add an FX0 certificate case after FX1 emits proof traces.

The current raw `hcomp` has only sides and cap payloads.  It does not yet carry
the boundary cofibration data needed for Kan computation rules, so this module
exports construction, projection, parallel congruence, and conversion
congruence only.  Any future β rule belongs here only after the raw payload is
strong enough to state the boundary condition being reduced.
-/

namespace LeanFX2
namespace Cubical

/-- Named homogeneous composition redex.

This is a cubical-layer API over the primitive typed `Term.hcomp` constructor.
Keeping the name here prevents downstream code from reaching directly for raw
payloads when it only needs homogeneous composition over one carrier type. -/
def homogeneousComposition {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw) :
    Term context carrierType (RawTerm.hcomp sidesRaw capRaw) :=
  Term.hcomp sidesValue capValue

/-- `homogeneousComposition` projects to the corresponding raw `hcomp`
payload. -/
theorem homogeneousComposition_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw) :
    (homogeneousComposition sidesValue capValue).toRaw =
      RawTerm.hcomp sidesRaw capRaw :=
  rfl

/-- Parallel congruence for the named homogeneous-composition redex. -/
theorem homogeneousComposition_parCong {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {sidesRawSource sidesRawTarget capRawSource capRawTarget : RawTerm scope}
    {sidesSource : Term context carrierType sidesRawSource}
    {sidesTarget : Term context carrierType sidesRawTarget}
    {capSource : Term context carrierType capRawSource}
    {capTarget : Term context carrierType capRawTarget}
    (sidesStep : Step.par sidesSource sidesTarget)
    (capStep : Step.par capSource capTarget) :
    Step.par
      (homogeneousComposition sidesSource capSource)
      (homogeneousComposition sidesTarget capTarget) :=
  Step.par.hcompCong sidesStep capStep

/-- Conversion congruence for the named homogeneous-composition redex. -/
theorem homogeneousComposition_convCumul {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {sidesRawFirst sidesRawSecond capRawFirst capRawSecond : RawTerm scope}
    {sidesFirst : Term context carrierType sidesRawFirst}
    {sidesSecond : Term context carrierType sidesRawSecond}
    {capFirst : Term context carrierType capRawFirst}
    {capSecond : Term context carrierType capRawSecond}
    (sidesRel : ConvCumul sidesFirst sidesSecond)
    (capRel : ConvCumul capFirst capSecond) :
    ConvCumul
      (homogeneousComposition sidesFirst capFirst)
      (homogeneousComposition sidesSecond capSecond) :=
  ConvCumul.hcompCong sidesRel capRel

/-- Degenerate homogeneous composition where the side payload is the cap.

This is not a β rule and does not claim that `hcomp cap cap` reduces to `cap`.
It is only the canonical named redex shape that future boundary-aware hcomp
computation can target. -/
def degenerateHomogeneousComposition {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {capRaw : RawTerm scope}
    (capValue : Term context carrierType capRaw) :
    Term context carrierType (RawTerm.hcomp capRaw capRaw) :=
  homogeneousComposition capValue capValue

/-- The degenerate hcomp redex projects to `RawTerm.hcomp cap cap`. -/
theorem degenerateHomogeneousComposition_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {capRaw : RawTerm scope}
    (capValue : Term context carrierType capRaw) :
    (degenerateHomogeneousComposition capValue).toRaw =
      RawTerm.hcomp capRaw capRaw :=
  rfl

/-- Parallel congruence for the degenerate hcomp redex. -/
theorem degenerateHomogeneousComposition_parCong
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {capRawSource capRawTarget : RawTerm scope}
    {capSource : Term context carrierType capRawSource}
    {capTarget : Term context carrierType capRawTarget}
    (capStep : Step.par capSource capTarget) :
    Step.par
      (degenerateHomogeneousComposition capSource)
      (degenerateHomogeneousComposition capTarget) :=
  homogeneousComposition_parCong capStep capStep

/-- Conversion congruence for the degenerate hcomp redex. -/
theorem degenerateHomogeneousComposition_convCumul
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {capRawFirst capRawSecond : RawTerm scope}
    {capFirst : Term context carrierType capRawFirst}
    {capSecond : Term context carrierType capRawSecond}
    (capRel : ConvCumul capFirst capSecond) :
    ConvCumul
      (degenerateHomogeneousComposition capFirst)
      (degenerateHomogeneousComposition capSecond) :=
  homogeneousComposition_convCumul capRel capRel

end Cubical
end LeanFX2
