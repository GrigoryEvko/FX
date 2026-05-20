import LeanFX2.Term

/-! # Term/HEqCongr/Atomic/Cubical

Cubical atomic HEq congruences. -/

namespace LeanFX2

/-- HEq congruence for path introduction with shared univalence evidence. -/
theorem Term.pathLam_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType1 carrierType2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {bodyRaw1 bodyRaw2 : RawTerm (scope + 1)}
    (carrierTypeEq : carrierType1 = carrierType2)
    (leftEndpointEq : leftEndpoint1 = leftEndpoint2)
    (rightEndpointEq : rightEndpoint1 = rightEndpoint2)
    (bodyRawEq : bodyRaw1 = bodyRaw2)
    {body1 : Term (context.cons Ty.interval) carrierType1.weaken bodyRaw1}
    {body2 : Term (context.cons Ty.interval) carrierType2.weaken bodyRaw2}
    (bodyHEq : HEq body1 body2) :
    HEq
      (Term.pathLam modeIsUnivalent carrierType1 leftEndpoint1
        rightEndpoint1 body1)
      (Term.pathLam modeIsUnivalent carrierType2 leftEndpoint2
        rightEndpoint2 body2) := by
  subst carrierTypeEq
  subst leftEndpointEq
  subst rightEndpointEq
  subst bodyRawEq
  cases bodyHEq
  rfl

/-- HEq congruence for path application with shared univalence evidence. -/
theorem Term.pathApp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType1 carrierType2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 : RawTerm scope}
    {pathRaw1 pathRaw2 intervalRaw1 intervalRaw2 : RawTerm scope}
    (carrierTypeEq : carrierType1 = carrierType2)
    (leftEndpointEq : leftEndpoint1 = leftEndpoint2)
    (rightEndpointEq : rightEndpoint1 = rightEndpoint2)
    (pathRawEq : pathRaw1 = pathRaw2)
    (intervalRawEq : intervalRaw1 = intervalRaw2)
    {pathTerm1 :
      Term context (Ty.path carrierType1 leftEndpoint1 rightEndpoint1)
        pathRaw1}
    {pathTerm2 :
      Term context (Ty.path carrierType2 leftEndpoint2 rightEndpoint2)
        pathRaw2}
    (pathTermHEq : HEq pathTerm1 pathTerm2)
    {intervalTerm1 : Term context Ty.interval intervalRaw1}
    {intervalTerm2 : Term context Ty.interval intervalRaw2}
    (intervalTermHEq : HEq intervalTerm1 intervalTerm2) :
    HEq (Term.pathApp modeIsUnivalent pathTerm1 intervalTerm1)
      (Term.pathApp modeIsUnivalent pathTerm2 intervalTerm2) := by
  subst carrierTypeEq
  subst leftEndpointEq
  subst rightEndpointEq
  subst pathRawEq
  subst intervalRawEq
  cases pathTermHEq
  cases intervalTermHEq
  rfl

/-- HEq congruence for Glue introduction with shared univalence evidence. -/
theorem Term.glueIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType1 baseType2 : Ty level scope}
    {boundaryWitness1 boundaryWitness2 baseRaw1 baseRaw2 partialRaw1 partialRaw2 :
      RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (boundaryWitnessEq : boundaryWitness1 = boundaryWitness2)
    (baseRawEq : baseRaw1 = baseRaw2)
    (partialRawEq : partialRaw1 = partialRaw2)
    {baseValue1 : Term context baseType1 baseRaw1}
    {baseValue2 : Term context baseType2 baseRaw2}
    (baseValueHEq : HEq baseValue1 baseValue2)
    {partialValue1 : Term context baseType1 partialRaw1}
    {partialValue2 : Term context baseType2 partialRaw2}
    (partialValueHEq : HEq partialValue1 partialValue2) :
    HEq
      (Term.glueIntro modeIsUnivalent baseType1 boundaryWitness1
        baseValue1 partialValue1)
      (Term.glueIntro modeIsUnivalent baseType2 boundaryWitness2
        baseValue2 partialValue2) := by
  subst baseTypeEq
  subst boundaryWitnessEq
  subst baseRawEq
  subst partialRawEq
  cases baseValueHEq
  cases partialValueHEq
  rfl

/-- HEq congruence for Glue elimination with shared univalence evidence. -/
theorem Term.glueElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType1 baseType2 : Ty level scope}
    {boundaryWitness1 boundaryWitness2 gluedRaw1 gluedRaw2 : RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (boundaryWitnessEq : boundaryWitness1 = boundaryWitness2)
    (gluedRawEq : gluedRaw1 = gluedRaw2)
    {gluedValue1 : Term context (Ty.glue baseType1 boundaryWitness1) gluedRaw1}
    {gluedValue2 : Term context (Ty.glue baseType2 boundaryWitness2) gluedRaw2}
    (gluedValueHEq : HEq gluedValue1 gluedValue2) :
    HEq (Term.glueElim modeIsUnivalent gluedValue1)
      (Term.glueElim modeIsUnivalent gluedValue2) := by
  subst baseTypeEq
  subst boundaryWitnessEq
  subst gluedRawEq
  cases gluedValueHEq
  rfl

/-- HEq congruence for homogeneous composition. -/
theorem Term.hcomp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType1 carrierType2 : Ty level scope}
    {sidesRaw1 sidesRaw2 capRaw1 capRaw2 : RawTerm scope}
    (carrierTypeEq : carrierType1 = carrierType2)
    (sidesRawEq : sidesRaw1 = sidesRaw2)
    (capRawEq : capRaw1 = capRaw2)
    {sidesValue1 : Term context carrierType1 sidesRaw1}
    {sidesValue2 : Term context carrierType2 sidesRaw2}
    (sidesValueHEq : HEq sidesValue1 sidesValue2)
    {capValue1 : Term context carrierType1 capRaw1}
    {capValue2 : Term context carrierType2 capRaw2}
    (capValueHEq : HEq capValue1 capValue2) :
    HEq (Term.hcomp modeIsUnivalent sidesValue1 capValue1)
      (Term.hcomp modeIsUnivalent sidesValue2 capValue2) := by
  subst carrierTypeEq
  subst sidesRawEq
  subst capRawEq
  cases sidesValueHEq
  cases capValueHEq
  rfl

/-- HEq congruence for path-shaped homogeneous composition. -/
theorem Term.hcompPath_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType1 carrierType2 : Ty level scope}
    {leftEndpoint1 leftEndpoint2 rightEndpoint1 rightEndpoint2 :
      RawTerm scope}
    {sidesPathRaw1 sidesPathRaw2 capRaw1 capRaw2 : RawTerm scope}
    (carrierTypeEq : carrierType1 = carrierType2)
    (leftEndpointEq : leftEndpoint1 = leftEndpoint2)
    (rightEndpointEq : rightEndpoint1 = rightEndpoint2)
    (sidesPathRawEq : sidesPathRaw1 = sidesPathRaw2)
    (capRawEq : capRaw1 = capRaw2)
    {sidesPath1 :
      Term context (Ty.path carrierType1 leftEndpoint1 rightEndpoint1)
        sidesPathRaw1}
    {sidesPath2 :
      Term context (Ty.path carrierType2 leftEndpoint2 rightEndpoint2)
        sidesPathRaw2}
    (sidesPathHEq : HEq sidesPath1 sidesPath2)
    {capValue1 : Term context carrierType1 capRaw1}
    {capValue2 : Term context carrierType2 capRaw2}
    (capValueHEq : HEq capValue1 capValue2) :
    HEq
      (Term.hcompPath modeIsUnivalent leftEndpoint1 rightEndpoint1
        sidesPath1 capValue1)
      (Term.hcompPath modeIsUnivalent leftEndpoint2 rightEndpoint2
        sidesPath2 capValue2) := by
  subst carrierTypeEq
  subst leftEndpointEq
  subst rightEndpointEq
  subst sidesPathRawEq
  subst capRawEq
  cases sidesPathHEq
  cases capValueHEq
  rfl

/-- HEq congruence for cubical transport with shared univalence evidence. -/
theorem Term.transp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {sourceType1 sourceType2 targetType1 targetType2 : Ty level scope}
    {sourceTypeRaw1 sourceTypeRaw2 targetTypeRaw1 targetTypeRaw2 :
      RawTerm scope}
    {pathRaw1 pathRaw2 sourceRaw1 sourceRaw2 : RawTerm scope}
    (sourceTypeEq : sourceType1 = sourceType2)
    (targetTypeEq : targetType1 = targetType2)
    (sourceTypeRawEq : sourceTypeRaw1 = sourceTypeRaw2)
    (targetTypeRawEq : targetTypeRaw1 = targetTypeRaw2)
    (pathRawEq : pathRaw1 = pathRaw2)
    (sourceRawEq : sourceRaw1 = sourceRaw2)
    {typePath1 :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw1 targetTypeRaw1)
        pathRaw1}
    {typePath2 :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw2 targetTypeRaw2)
        pathRaw2}
    (typePathHEq : HEq typePath1 typePath2)
    {sourceValue1 : Term context sourceType1 sourceRaw1}
    {sourceValue2 : Term context sourceType2 sourceRaw2}
    (sourceValueHEq : HEq sourceValue1 sourceValue2) :
    HEq
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType1 targetType1 sourceTypeRaw1 targetTypeRaw1 typePath1
        sourceValue1)
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType2 targetType2 sourceTypeRaw2 targetTypeRaw2 typePath2
        sourceValue2) := by
  subst sourceTypeEq
  subst targetTypeEq
  subst sourceTypeRawEq
  subst targetTypeRawEq
  subst pathRawEq
  subst sourceRawEq
  cases typePathHEq
  cases sourceValueHEq
  rfl

end LeanFX2
