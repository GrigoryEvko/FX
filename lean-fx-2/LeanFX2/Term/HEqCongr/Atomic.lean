import LeanFX2.Term

/-! # Term/HEqCongr/Atomic — HEq congruence lemmas, atomic half

Split off from `LeanFX2/Term/HEqCongr.lean` together with
`Term/HEqCongr/Compound.lean`.  This half holds the 42 simpler
congruences: atomic nullary ctors (var, unit, boolTrue/False,
natZero, listNil, optionNone), interval primitives (0, 1, opp,
meet, join), cubical operators (pathLam, pathApp, glueIntro/Elim,
hcomp, transp), structural intros/elims (record, refine, codata,
session, effect), type-code values (universe through equiv),
and heterogeneous intros (equivIntroHet, uaIntroHet,
funextIntroHet).

Every theorem here keeps the same statement and proof body as
the pre-split monolith — verified by `#print axioms` gates in
`Smoke/AuditPhase2HEqCongr.lean`. -/

namespace LeanFX2

/-- HEq congruence for variables at equal positions. -/
theorem Term.var_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {position1 position2 : Fin scope}
    (positionEq : position1 = position2) :
    HEq (Term.var (context := context) position1)
      (Term.var (context := context) position2) := by
  subst positionEq
  rfl

/-- HEq congruence for `Term.unit`. -/
theorem Term.unit_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.unit (context := context)) (Term.unit (context := context)) := by
  rfl

/-- HEq congruence for `Term.boolTrue`. -/
theorem Term.boolTrue_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.boolTrue (context := context))
      (Term.boolTrue (context := context)) := by
  rfl

/-- HEq congruence for `Term.boolFalse`. -/
theorem Term.boolFalse_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.boolFalse (context := context))
      (Term.boolFalse (context := context)) := by
  rfl

/-- HEq congruence for `Term.natZero`. -/
theorem Term.natZero_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.natZero (context := context))
      (Term.natZero (context := context)) := by
  rfl

/-- HEq congruence for `Term.listNil`. -/
theorem Term.listNil_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    (elementTypeEq : elementType1 = elementType2) :
    HEq (Term.listNil (context := context) (elementType := elementType1))
      (Term.listNil (context := context) (elementType := elementType2)) := by
  subst elementTypeEq
  rfl

/-- HEq congruence for `Term.optionNone`. -/
theorem Term.optionNone_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {elementType1 elementType2 : Ty level scope}
    (elementTypeEq : elementType1 = elementType2) :
    HEq (Term.optionNone (context := context) (elementType := elementType1))
      (Term.optionNone (context := context) (elementType := elementType2)) := by
  subst elementTypeEq
  rfl

/-- HEq congruence for `Term.interval0`. -/
theorem Term.interval0_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.interval0 (context := context))
      (Term.interval0 (context := context)) := by
  rfl

/-- HEq congruence for `Term.interval1`. -/
theorem Term.interval1_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    HEq (Term.interval1 (context := context))
      (Term.interval1 (context := context)) := by
  rfl

/-- HEq congruence for interval negation. -/
theorem Term.intervalOpp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {innerRaw1 innerRaw2 : RawTerm scope}
    (innerRawEq : innerRaw1 = innerRaw2)
    {innerValue1 : Term context Ty.interval innerRaw1}
    {innerValue2 : Term context Ty.interval innerRaw2}
    (innerValueHEq : HEq innerValue1 innerValue2) :
    HEq (Term.intervalOpp innerValue1) (Term.intervalOpp innerValue2) := by
  subst innerRawEq
  cases innerValueHEq
  rfl

/-- HEq congruence for interval meet. -/
theorem Term.intervalMeet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {leftValue1 : Term context Ty.interval leftRaw1}
    {leftValue2 : Term context Ty.interval leftRaw2}
    (leftValueHEq : HEq leftValue1 leftValue2)
    {rightValue1 : Term context Ty.interval rightRaw1}
    {rightValue2 : Term context Ty.interval rightRaw2}
    (rightValueHEq : HEq rightValue1 rightValue2) :
    HEq (Term.intervalMeet leftValue1 rightValue1)
      (Term.intervalMeet leftValue2 rightValue2) := by
  subst leftRawEq
  subst rightRawEq
  cases leftValueHEq
  cases rightValueHEq
  rfl

/-- HEq congruence for interval join. -/
theorem Term.intervalJoin_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {leftRaw1 leftRaw2 rightRaw1 rightRaw2 : RawTerm scope}
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2)
    {leftValue1 : Term context Ty.interval leftRaw1}
    {leftValue2 : Term context Ty.interval leftRaw2}
    (leftValueHEq : HEq leftValue1 leftValue2)
    {rightValue1 : Term context Ty.interval rightRaw1}
    {rightValue2 : Term context Ty.interval rightRaw2}
    (rightValueHEq : HEq rightValue1 rightValue2) :
    HEq (Term.intervalJoin leftValue1 rightValue1)
      (Term.intervalJoin leftValue2 rightValue2) := by
  subst leftRawEq
  subst rightRawEq
  cases leftValueHEq
  cases rightValueHEq
  rfl

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

/-- HEq congruence for single-field record introduction. -/
theorem Term.recordIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType1 singleFieldType2 : Ty level scope}
    {firstRaw1 firstRaw2 : RawTerm scope}
    (singleFieldTypeEq : singleFieldType1 = singleFieldType2)
    (firstRawEq : firstRaw1 = firstRaw2)
    {firstField1 : Term context singleFieldType1 firstRaw1}
    {firstField2 : Term context singleFieldType2 firstRaw2}
    (firstFieldHEq : HEq firstField1 firstField2) :
    HEq (Term.recordIntro firstField1) (Term.recordIntro firstField2) := by
  subst singleFieldTypeEq
  subst firstRawEq
  cases firstFieldHEq
  rfl

/-- HEq congruence for single-field record projection. -/
theorem Term.recordProj_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType1 singleFieldType2 : Ty level scope}
    {recordRaw1 recordRaw2 : RawTerm scope}
    (singleFieldTypeEq : singleFieldType1 = singleFieldType2)
    (recordRawEq : recordRaw1 = recordRaw2)
    {recordValue1 : Term context (Ty.record singleFieldType1) recordRaw1}
    {recordValue2 : Term context (Ty.record singleFieldType2) recordRaw2}
    (recordValueHEq : HEq recordValue1 recordValue2) :
    HEq (Term.recordProj recordValue1) (Term.recordProj recordValue2) := by
  subst singleFieldTypeEq
  subst recordRawEq
  cases recordValueHEq
  rfl

/-- HEq congruence for refinement elimination. -/
theorem Term.refineElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {baseType1 baseType2 : Ty level scope}
    {predicate1 predicate2 : RawTerm (scope + 1)}
    {refinedRaw1 refinedRaw2 : RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (predicateEq : predicate1 = predicate2)
    (refinedRawEq : refinedRaw1 = refinedRaw2)
    {refinedValue1 : Term context (Ty.refine baseType1 predicate1) refinedRaw1}
    {refinedValue2 : Term context (Ty.refine baseType2 predicate2) refinedRaw2}
    (refinedValueHEq : HEq refinedValue1 refinedValue2) :
    HEq (Term.refineElim refinedValue1) (Term.refineElim refinedValue2) := by
  subst baseTypeEq
  subst predicateEq
  subst refinedRawEq
  cases refinedValueHEq
  rfl

/-- HEq congruence for codata destruction. -/
theorem Term.codataDest_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {stateType1 stateType2 outputType1 outputType2 : Ty level scope}
    {codataRaw1 codataRaw2 : RawTerm scope}
    (stateTypeEq : stateType1 = stateType2)
    (outputTypeEq : outputType1 = outputType2)
    (codataRawEq : codataRaw1 = codataRaw2)
    {codataValue1 : Term context (Ty.codata stateType1 outputType1) codataRaw1}
    {codataValue2 : Term context (Ty.codata stateType2 outputType2) codataRaw2}
    (codataValueHEq : HEq codataValue1 codataValue2) :
    HEq (Term.codataDest codataValue1) (Term.codataDest codataValue2) := by
  subst stateTypeEq
  subst outputTypeEq
  subst codataRawEq
  cases codataValueHEq
  rfl

/-- HEq congruence for session receive. -/
theorem Term.sessionRecv_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {protocolStep1 protocolStep2 channelRaw1 channelRaw2 : RawTerm scope}
    (protocolStepEq : protocolStep1 = protocolStep2)
    (channelRawEq : channelRaw1 = channelRaw2)
    {channel1 : Term context (Ty.session protocolStep1) channelRaw1}
    {channel2 : Term context (Ty.session protocolStep2) channelRaw2}
    (channelHEq : HEq channel1 channel2) :
    HEq (Term.sessionRecv channel1) (Term.sessionRecv channel2) := by
  subst protocolStepEq
  subst channelRawEq
  cases channelHEq
  rfl

/-- HEq congruence for equivalence application. -/
theorem Term.equivApp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {equivRaw1 equivRaw2 argumentRaw1 argumentRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (equivRawEq : equivRaw1 = equivRaw2)
    (argumentRawEq : argumentRaw1 = argumentRaw2)
    {equivTerm1 : Term context (Ty.equiv carrierA1 carrierB1) equivRaw1}
    {equivTerm2 : Term context (Ty.equiv carrierA2 carrierB2) equivRaw2}
    (equivHEq : HEq equivTerm1 equivTerm2)
    {argumentTerm1 : Term context carrierA1 argumentRaw1}
    {argumentTerm2 : Term context carrierA2 argumentRaw2}
    (argumentHEq : HEq argumentTerm1 argumentTerm2) :
    HEq (Term.equivApp equivTerm1 argumentTerm1)
      (Term.equivApp equivTerm2 argumentTerm2) := by
  subst carrierAEq
  subst carrierBEq
  subst equivRawEq
  subst argumentRawEq
  cases equivHEq
  cases argumentHEq
  rfl

/-- HEq congruence for universe-code values with shared proof fields. -/
theorem Term.universeCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    HEq
      (Term.universeCode (context := context) innerLevel outerLevel cumulOk
        levelLe)
      (Term.universeCode (context := context) innerLevel outerLevel cumulOk
        levelLe) := by
  rfl

/-- HEq congruence for arrow type-code values. -/
theorem Term.arrowCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw1 domainCodeRaw2 codomainCodeRaw1 codomainCodeRaw2 :
      RawTerm scope}
    (domainCodeRawEq : domainCodeRaw1 = domainCodeRaw2)
    (codomainCodeRawEq : codomainCodeRaw1 = codomainCodeRaw2) :
    HEq
      (Term.arrowCode (context := context) outerLevel levelLe domainCodeRaw1
        codomainCodeRaw1)
      (Term.arrowCode (context := context) outerLevel levelLe domainCodeRaw2
        codomainCodeRaw2) := by
  subst domainCodeRawEq
  subst codomainCodeRawEq
  rfl

/-- HEq congruence for pi type-code values. -/
theorem Term.piTyCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw1 domainCodeRaw2 : RawTerm scope}
    {codomainCodeRaw1 codomainCodeRaw2 : RawTerm (scope + 1)}
    (domainCodeRawEq : domainCodeRaw1 = domainCodeRaw2)
    (codomainCodeRawEq : codomainCodeRaw1 = codomainCodeRaw2) :
    HEq
      (Term.piTyCode (context := context) outerLevel levelLe domainCodeRaw1
        codomainCodeRaw1)
      (Term.piTyCode (context := context) outerLevel levelLe domainCodeRaw2
        codomainCodeRaw2) := by
  subst domainCodeRawEq
  subst codomainCodeRawEq
  rfl

/-- HEq congruence for sigma type-code values. -/
theorem Term.sigmaTyCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw1 domainCodeRaw2 : RawTerm scope}
    {codomainCodeRaw1 codomainCodeRaw2 : RawTerm (scope + 1)}
    (domainCodeRawEq : domainCodeRaw1 = domainCodeRaw2)
    (codomainCodeRawEq : codomainCodeRaw1 = codomainCodeRaw2) :
    HEq
      (Term.sigmaTyCode (context := context) outerLevel levelLe domainCodeRaw1
        codomainCodeRaw1)
      (Term.sigmaTyCode (context := context) outerLevel levelLe domainCodeRaw2
        codomainCodeRaw2) := by
  subst domainCodeRawEq
  subst codomainCodeRawEq
  rfl

/-- HEq congruence for product type-code values. -/
theorem Term.productCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw1 firstCodeRaw2 secondCodeRaw1 secondCodeRaw2 :
      RawTerm scope}
    (firstCodeRawEq : firstCodeRaw1 = firstCodeRaw2)
    (secondCodeRawEq : secondCodeRaw1 = secondCodeRaw2) :
    HEq
      (Term.productCode (context := context) outerLevel levelLe firstCodeRaw1
        secondCodeRaw1)
      (Term.productCode (context := context) outerLevel levelLe firstCodeRaw2
        secondCodeRaw2) := by
  subst firstCodeRawEq
  subst secondCodeRawEq
  rfl

/-- HEq congruence for sum type-code values. -/
theorem Term.sumCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw1 leftCodeRaw2 rightCodeRaw1 rightCodeRaw2 : RawTerm scope}
    (leftCodeRawEq : leftCodeRaw1 = leftCodeRaw2)
    (rightCodeRawEq : rightCodeRaw1 = rightCodeRaw2) :
    HEq
      (Term.sumCode (context := context) outerLevel levelLe leftCodeRaw1
        rightCodeRaw1)
      (Term.sumCode (context := context) outerLevel levelLe leftCodeRaw2
        rightCodeRaw2) := by
  subst leftCodeRawEq
  subst rightCodeRawEq
  rfl

/-- HEq congruence for list type-code values. -/
theorem Term.listCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw1 elementCodeRaw2 : RawTerm scope}
    (elementCodeRawEq : elementCodeRaw1 = elementCodeRaw2) :
    HEq
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw1)
      (Term.listCode (context := context) outerLevel levelLe
        elementCodeRaw2) := by
  subst elementCodeRawEq
  rfl

/-- HEq congruence for option type-code values. -/
theorem Term.optionCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw1 elementCodeRaw2 : RawTerm scope}
    (elementCodeRawEq : elementCodeRaw1 = elementCodeRaw2) :
    HEq
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw1)
      (Term.optionCode (context := context) outerLevel levelLe
        elementCodeRaw2) := by
  subst elementCodeRawEq
  rfl

/-- HEq congruence for either type-code values. -/
theorem Term.eitherCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw1 leftCodeRaw2 rightCodeRaw1 rightCodeRaw2 : RawTerm scope}
    (leftCodeRawEq : leftCodeRaw1 = leftCodeRaw2)
    (rightCodeRawEq : rightCodeRaw1 = rightCodeRaw2) :
    HEq
      (Term.eitherCode (context := context) outerLevel levelLe leftCodeRaw1
        rightCodeRaw1)
      (Term.eitherCode (context := context) outerLevel levelLe leftCodeRaw2
        rightCodeRaw2) := by
  subst leftCodeRawEq
  subst rightCodeRawEq
  rfl

/-- HEq congruence for identity type-code values. -/
theorem Term.idCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw1 typeCodeRaw2 leftRaw1 leftRaw2 rightRaw1 rightRaw2 :
      RawTerm scope}
    (typeCodeRawEq : typeCodeRaw1 = typeCodeRaw2)
    (leftRawEq : leftRaw1 = leftRaw2)
    (rightRawEq : rightRaw1 = rightRaw2) :
    HEq
      (Term.idCode (context := context) outerLevel levelLe typeCodeRaw1
        leftRaw1 rightRaw1)
      (Term.idCode (context := context) outerLevel levelLe typeCodeRaw2
        leftRaw2 rightRaw2) := by
  subst typeCodeRawEq
  subst leftRawEq
  subst rightRawEq
  rfl

/-- HEq congruence for equivalence type-code values. -/
theorem Term.equivCode_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw1 leftTypeCodeRaw2 rightTypeCodeRaw1 rightTypeCodeRaw2 :
      RawTerm scope}
    (leftTypeCodeRawEq : leftTypeCodeRaw1 = leftTypeCodeRaw2)
    (rightTypeCodeRawEq : rightTypeCodeRaw1 = rightTypeCodeRaw2) :
    HEq
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw1 rightTypeCodeRaw1)
      (Term.equivCode (context := context) outerLevel levelLe
        leftTypeCodeRaw2 rightTypeCodeRaw2) := by
  subst leftTypeCodeRawEq
  subst rightTypeCodeRawEq
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

/-- HEq congruence for refinement introduction. -/
theorem Term.refineIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {baseType1 baseType2 : Ty level scope}
    {predicate1 predicate2 : RawTerm (scope + 1)}
    {valueRaw1 valueRaw2 proofRaw1 proofRaw2 : RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (predicateEq : predicate1 = predicate2)
    (valueRawEq : valueRaw1 = valueRaw2)
    (proofRawEq : proofRaw1 = proofRaw2)
    {baseValue1 : Term context baseType1 valueRaw1}
    {baseValue2 : Term context baseType2 valueRaw2}
    (baseValueHEq : HEq baseValue1 baseValue2)
    {predicateProof1 : Term context Ty.unit proofRaw1}
    {predicateProof2 : Term context Ty.unit proofRaw2}
    (predicateProofHEq : HEq predicateProof1 predicateProof2) :
    HEq (Term.refineIntro predicate1 baseValue1 predicateProof1)
      (Term.refineIntro predicate2 baseValue2 predicateProof2) := by
  subst baseTypeEq
  subst predicateEq
  subst valueRawEq
  subst proofRawEq
  cases baseValueHEq
  cases predicateProofHEq
  rfl

/-- HEq congruence for codata unfold. -/
theorem Term.codataUnfold_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {stateType1 stateType2 outputType1 outputType2 : Ty level scope}
    {stateRaw1 stateRaw2 transitionRaw1 transitionRaw2 : RawTerm scope}
    (stateTypeEq : stateType1 = stateType2)
    (outputTypeEq : outputType1 = outputType2)
    (stateRawEq : stateRaw1 = stateRaw2)
    (transitionRawEq : transitionRaw1 = transitionRaw2)
    {initialState1 : Term context stateType1 stateRaw1}
    {initialState2 : Term context stateType2 stateRaw2}
    (initialStateHEq : HEq initialState1 initialState2)
    {transition1 : Term context (Ty.arrow stateType1 outputType1) transitionRaw1}
    {transition2 : Term context (Ty.arrow stateType2 outputType2) transitionRaw2}
    (transitionHEq : HEq transition1 transition2) :
    HEq (Term.codataUnfold initialState1 transition1)
      (Term.codataUnfold initialState2 transition2) := by
  subst stateTypeEq
  subst outputTypeEq
  subst stateRawEq
  subst transitionRawEq
  cases initialStateHEq
  cases transitionHEq
  rfl

/-- HEq congruence for session send. -/
theorem Term.sessionSend_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {protocolStep1 protocolStep2 : RawTerm scope}
    {payloadType1 payloadType2 : Ty level scope}
    {channelRaw1 channelRaw2 payloadRaw1 payloadRaw2 : RawTerm scope}
    (protocolStepEq : protocolStep1 = protocolStep2)
    (payloadTypeEq : payloadType1 = payloadType2)
    (channelRawEq : channelRaw1 = channelRaw2)
    (payloadRawEq : payloadRaw1 = payloadRaw2)
    {channel1 : Term context (Ty.session protocolStep1) channelRaw1}
    {channel2 : Term context (Ty.session protocolStep2) channelRaw2}
    (channelHEq : HEq channel1 channel2)
    {payload1 : Term context payloadType1 payloadRaw1}
    {payload2 : Term context payloadType2 payloadRaw2}
    (payloadHEq : HEq payload1 payload2) :
    HEq (Term.sessionSend protocolStep1 channel1 payload1)
      (Term.sessionSend protocolStep2 channel2 payload2) := by
  subst protocolStepEq
  subst payloadTypeEq
  subst channelRawEq
  subst payloadRawEq
  cases channelHEq
  cases payloadHEq
  rfl

/-- HEq congruence for effect performance with shared row evidence. -/
theorem Term.effectPerform_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 : RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 :
      Term context operationSignature.argumentCarrier argumentsRaw1}
    {arguments2 :
      Term context operationSignature.argumentCarrier argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow operationSignature
        canPerformOperation operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow operationSignature
        canPerformOperation operationTag2 arguments2) := by
  subst effectTagEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

/-- HEq congruence for heterogeneous equivalence introduction. -/
theorem Term.equivIntroHet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {forwardRaw1 forwardRaw2 backwardRaw1 backwardRaw2 : RawTerm scope}
    {leftInvRaw1 leftInvRaw2 rightInvRaw1 rightInvRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (forwardRawEq : forwardRaw1 = forwardRaw2)
    (backwardRawEq : backwardRaw1 = backwardRaw2)
    (leftInvRawEq : leftInvRaw1 = leftInvRaw2)
    (rightInvRawEq : rightInvRaw1 = rightInvRaw2)
    {forward1 : Term context (Ty.arrow carrierA1 carrierB1) forwardRaw1}
    {forward2 : Term context (Ty.arrow carrierA2 carrierB2) forwardRaw2}
    (forwardHEq : HEq forward1 forward2)
    {backward1 : Term context (Ty.arrow carrierB1 carrierA1) backwardRaw1}
    {backward2 : Term context (Ty.arrow carrierB2 carrierA2) backwardRaw2}
    (backwardHEq : HEq backward1 backward2)
    {leftInv1 :
      Term context
        (equivIntroHetLeftInverseType carrierA1 forwardRaw1 backwardRaw1)
        leftInvRaw1}
    {leftInv2 :
      Term context
        (equivIntroHetLeftInverseType carrierA2 forwardRaw2 backwardRaw2)
        leftInvRaw2}
    (leftInvHEq : HEq leftInv1 leftInv2)
    {rightInv1 :
      Term context
        (equivIntroHetRightInverseType carrierB1 forwardRaw1 backwardRaw1)
        rightInvRaw1}
    {rightInv2 :
      Term context
        (equivIntroHetRightInverseType carrierB2 forwardRaw2 backwardRaw2)
        rightInvRaw2}
    (rightInvHEq : HEq rightInv1 rightInv2) :
    HEq (Term.equivIntroHet forward1 backward1 leftInv1 rightInv1)
      (Term.equivIntroHet forward2 backward2 leftInv2 rightInv2) := by
  subst carrierAEq
  subst carrierBEq
  subst forwardRawEq
  subst backwardRawEq
  subst leftInvRawEq
  subst rightInvRawEq
  cases forwardHEq
  cases backwardHEq
  cases leftInvHEq
  cases rightInvHEq
  rfl

/-- HEq congruence for heterogeneous univalence introduction. -/
theorem Term.uaIntroHet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {carrierARaw1 carrierARaw2 carrierBRaw1 carrierBRaw2 : RawTerm scope}
    {forwardRaw1 forwardRaw2 backwardRaw1 backwardRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (carrierARawEq : carrierARaw1 = carrierARaw2)
    (carrierBRawEq : carrierBRaw1 = carrierBRaw2)
    (forwardRawEq : forwardRaw1 = forwardRaw2)
    (backwardRawEq : backwardRaw1 = backwardRaw2)
    {equivWitness1 :
      Term context (Ty.equiv carrierA1 carrierB1)
        (RawTerm.equivIntro forwardRaw1 backwardRaw1)}
    {equivWitness2 :
      Term context (Ty.equiv carrierA2 carrierB2)
        (RawTerm.equivIntro forwardRaw2 backwardRaw2)}
    (equivWitnessHEq : HEq equivWitness1 equivWitness2) :
    HEq
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw1 carrierBRaw1
        equivWitness1)
      (Term.uaIntroHet innerLevel innerLevelLt carrierARaw2 carrierBRaw2
        equivWitness2) := by
  subst carrierAEq
  subst carrierBEq
  subst carrierARawEq
  subst carrierBRawEq
  subst forwardRawEq
  subst backwardRawEq
  cases equivWitnessHEq
  rfl

/-- HEq congruence for heterogeneous funext introduction. -/
theorem Term.funextIntroHet_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType1 domainType2 codomainType1 codomainType2 : Ty level scope}
    {applyARaw1 applyARaw2 applyBRaw1 applyBRaw2 : RawTerm (scope + 1)}
    (domainEq : domainType1 = domainType2)
    (codomainEq : codomainType1 = codomainType2)
    (applyARawEq : applyARaw1 = applyARaw2)
    (applyBRawEq : applyBRaw1 = applyBRaw2) :
    HEq
      (Term.funextIntroHet (context := context) domainType1 codomainType1
        applyARaw1 applyBRaw1)
      (Term.funextIntroHet (context := context) domainType2 codomainType2
        applyARaw2 applyBRaw2) := by
  subst domainEq
  subst codomainEq
  subst applyARawEq
  subst applyBRawEq
  rfl

end LeanFX2
