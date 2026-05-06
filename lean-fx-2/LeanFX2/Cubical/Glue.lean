import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.Cumul

/-! # Cubical/Glue

Glue helpers for the current rich-layer cubical fragment.

Root status: FX-rich.

Bridge obligations:
* add `Ty.glue`, `RawTerm.glueIntro`, and `RawTerm.glueElim` cases to the FX1
  rich-fragment encoders;
* add typed introduction, elimination, congruence, and β soundness cases once
  rich terms are bridged into FX1;
* add an FX0 certificate case after FX1 emits proof traces.

This module exposes exactly the Glue structure already present in the typed
kernel: introduction, elimination, congruence, and the safe eliminator-after-
introduction β rule.  It does not add face-specific Glue computation rules;
those require a richer boundary/cofibration payload.
-/

namespace LeanFX2
namespace Cubical

/-- Named Glue introduction redex. -/
def glueIntroduction {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw) :
    Term context (Ty.glue baseType boundaryWitness)
      (RawTerm.glueIntro baseRaw partialRaw) :=
  Term.glueIntro baseType boundaryWitness baseValue partialValue

/-- `glueIntroduction` projects to the corresponding raw Glue intro payload. -/
theorem glueIntroduction_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw) :
    (glueIntroduction boundaryWitness baseValue partialValue).toRaw =
      RawTerm.glueIntro baseRaw partialRaw :=
  rfl

/-- Named Glue eliminator redex. -/
def glueElimination {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw) :
    Term context baseType (RawTerm.glueElim gluedRaw) :=
  Term.glueElim gluedValue

/-- `glueElimination` projects to the corresponding raw Glue eliminator
payload. -/
theorem glueElimination_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw) :
    (glueElimination gluedValue).toRaw = RawTerm.glueElim gluedRaw :=
  rfl

/-- Parallel congruence for the named Glue introduction redex. -/
theorem glueIntroduction_parCong {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (boundaryWitness : RawTerm scope)
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm scope}
    {baseSource : Term context baseType baseRawSource}
    {baseTarget : Term context baseType baseRawTarget}
    {partialSource : Term context baseType partialRawSource}
    {partialTarget : Term context baseType partialRawTarget}
    (baseStep : Step.par baseSource baseTarget)
    (partialStep : Step.par partialSource partialTarget) :
    Step.par
      (glueIntroduction boundaryWitness baseSource partialSource)
      (glueIntroduction boundaryWitness baseTarget partialTarget) :=
  Step.par.glueIntroCong baseStep partialStep

/-- Parallel congruence for the named Glue eliminator redex. -/
theorem glueElimination_parCong {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRawSource gluedRawTarget : RawTerm scope}
    {gluedSource :
      Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term context (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (gluedStep : Step.par gluedSource gluedTarget) :
    Step.par
      (glueElimination gluedSource)
      (glueElimination gluedTarget) :=
  Step.par.glueElimCong gluedStep

/-- Conversion congruence for the named Glue introduction redex. -/
theorem glueIntroduction_convCumul {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (boundaryWitness : RawTerm scope)
    {baseRawFirst baseRawSecond partialRawFirst partialRawSecond :
      RawTerm scope}
    {baseFirst : Term context baseType baseRawFirst}
    {baseSecond : Term context baseType baseRawSecond}
    {partialFirst : Term context baseType partialRawFirst}
    {partialSecond : Term context baseType partialRawSecond}
    (baseRel : ConvCumul baseFirst baseSecond)
    (partialRel : ConvCumul partialFirst partialSecond) :
    ConvCumul
      (glueIntroduction boundaryWitness baseFirst partialFirst)
      (glueIntroduction boundaryWitness baseSecond partialSecond) :=
  ConvCumul.glueIntroCong baseRel partialRel

/-- Conversion congruence for the named Glue eliminator redex. -/
theorem glueElimination_convCumul {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRawFirst gluedRawSecond : RawTerm scope}
    {gluedFirst :
      Term context (Ty.glue baseType boundaryWitness) gluedRawFirst}
    {gluedSecond :
      Term context (Ty.glue baseType boundaryWitness) gluedRawSecond}
    (gluedRel : ConvCumul gluedFirst gluedSecond) :
    ConvCumul
      (glueElimination gluedFirst)
      (glueElimination gluedSecond) :=
  ConvCumul.glueElimCong gluedRel

/-- Parallel β for `glueElimination (glueIntroduction base partial)`. -/
theorem glueElimIntro_parBeta {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw) :
    Step.par
      (glueElimination
        (glueIntroduction boundaryWitness baseValue partialValue))
      baseValue :=
  Step.par.betaGlueElimIntro (Step.par.refl _) (Step.par.refl _)

/-- Conversion β for `glueElimination (glueIntroduction base partial)`. -/
theorem glueElimIntro_convCumulBeta {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw) :
    ConvCumul
      (glueElimination
        (glueIntroduction boundaryWitness baseValue partialValue))
      baseValue :=
  ConvCumul.betaGlueElimIntroCumul baseValue partialValue

end Cubical
end LeanFX2
