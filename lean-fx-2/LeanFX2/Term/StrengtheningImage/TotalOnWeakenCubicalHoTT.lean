import LeanFX2.Term.StrengtheningImage.TotalOnWeakenRecursive

/-! # Term/StrengtheningImage/TotalOnWeakenCubicalHoTT

Total-on-weaken wrappers for cubical and heterogeneous HoTT constructors.
-/

namespace LeanFX2

namespace Term

/-! ## Wave D: cubical / HoTT non-binder totality. -/

/-- 0-IH parametric atomic totality: `Term.equivReflId`.  One Ty
sub-payload (carrier), no Term IH. -/
theorem isTotalOnWeaken_equivReflId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) :
    IsTotalOnWeaken (Term.equivReflId (context := context) carrier) := by
  intro newType
  show (strengthenTyped? (Term.equivReflId
      (context := context.cons newType) carrier.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · rfl

/-- 0-IH parametric atomic totality: `Term.equivReflIdAtId`.  One Ty
+ one RawTerm sub-payload, no Term IH. -/
theorem isTotalOnWeaken_equivReflIdAtId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope) (carrierRaw : RawTerm scope) :
    IsTotalOnWeaken (Term.equivReflIdAtId (context := context)
      innerLevel innerLevelLt carrier carrierRaw) := by
  intro newType
  show (strengthenTyped? (Term.equivReflIdAtId
      (context := context.cons newType) innerLevel innerLevelLt
      carrier.weaken carrierRaw.weaken)).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrier.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrier :=
        Ty.strengthen?_weaken carrier
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next carrierRawFails =>
        exfalso
        have carrierRawSuccess :
            carrierRaw.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierRaw :=
          RawTerm.strengthen?_weaken carrierRaw
        rw [carrierRawSuccess] at carrierRawFails
        cases carrierRawFails
    · rfl

/-- 1-IH non-binder totality: `Term.glueElim`.  One Ty (baseType) +
one RawTerm (boundaryWitness) + one Term IH (gluedValue). -/
theorem isTotalOnWeaken_glueElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIH : IsTotalOnWeaken gluedValue) :
    IsTotalOnWeaken (Term.glueElim modeIsUnivalent gluedValue) := by
  intro newType
  show (strengthenTyped? (Term.glueElim modeIsUnivalent
      (Term.weaken newType gluedValue))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next boundaryFails =>
        exfalso
        have boundarySuccess :
            boundaryWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some boundaryWitness :=
          RawTerm.strengthen?_weaken boundaryWitness
        rw [boundarySuccess] at boundaryFails
        cases boundaryFails
    · split
      · next gluedRecurse =>
          exfalso
          have totHyp := gluedIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType gluedValue))) = true :=
            gluedRecurse ▸ totHyp
          cases this
      · rfl

/-- 2-IH non-binder totality: `Term.hcomp`.  No Ty payloads in the
dispatcher arm — purely 2-IH. -/
theorem isTotalOnWeaken_hcomp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    {sidesValue : Term context carrierType sidesRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIH : IsTotalOnWeaken sidesValue)
    (capIH : IsTotalOnWeaken capValue) :
    IsTotalOnWeaken (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  intro newType
  show (strengthenTyped? (Term.hcomp modeIsUnivalent
      (Term.weaken newType sidesValue)
      (Term.weaken newType capValue))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next sidesRecurse =>
      exfalso
      have totHyp := sidesIH newType
      dsimp only [strengthenTyped?] at totHyp
      have : Option.isSome (none (α := StrengtheningResult
          (ContextStrengthening.dropNewest context newType)
          (Term.weaken newType sidesValue))) = true :=
        sidesRecurse ▸ totHyp
      cases this
  · split
    · next capRecurse =>
        exfalso
        have totHyp := capIH newType
        dsimp only [strengthenTyped?] at totHyp
        have : Option.isSome (none (α := StrengtheningResult
            (ContextStrengthening.dropNewest context newType)
            (Term.weaken newType capValue))) = true :=
          capRecurse ▸ totHyp
        cases this
    · rfl

/-- 2-IH non-binder totality: `Term.glueIntro`.  One Ty (baseType) +
one RawTerm (boundaryWitness) + two Term IH (baseValue, partialValue). -/
theorem isTotalOnWeaken_glueIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIH : IsTotalOnWeaken baseValue)
    (partialIH : IsTotalOnWeaken partialValue) :
    IsTotalOnWeaken (Term.glueIntro modeIsUnivalent baseType
      boundaryWitness baseValue partialValue) := by
  intro newType
  show (strengthenTyped? (Term.glueIntro modeIsUnivalent
      baseType.weaken boundaryWitness.weaken
      (Term.weaken newType baseValue)
      (Term.weaken newType partialValue))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next baseFails =>
      exfalso
      have baseSuccess :
          baseType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some baseType :=
        Ty.strengthen?_weaken baseType
      rw [baseSuccess] at baseFails
      cases baseFails
  · split
    · next boundaryFails =>
        exfalso
        have boundarySuccess :
            boundaryWitness.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some boundaryWitness :=
          RawTerm.strengthen?_weaken boundaryWitness
        rw [boundarySuccess] at boundaryFails
        cases boundaryFails
    · split
      · next baseRecurse =>
          exfalso
          have totHyp := baseIH newType
          dsimp only [strengthenTyped?] at totHyp
          have : Option.isSome (none (α := StrengtheningResult
              (ContextStrengthening.dropNewest context newType)
              (Term.weaken newType baseValue))) = true :=
            baseRecurse ▸ totHyp
          cases this
      · split
        · next partialRecurse =>
            exfalso
            have totHyp := partialIH newType
            dsimp only [strengthenTyped?] at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType partialValue))) = true :=
              partialRecurse ▸ totHyp
            cases this
        · rfl

/-- 2-IH non-binder totality: `Term.transp`.  Two Ty (sourceType,
targetType) + two RawTerm (sourceTypeRaw, targetTypeRaw) + two Term
IH (typePath, sourceValue). -/
theorem isTotalOnWeaken_transp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    {typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (pathIH : IsTotalOnWeaken typePath)
    (sourceIH : IsTotalOnWeaken sourceValue) :
    IsTotalOnWeaken (Term.transp modeIsUnivalent universeLevel
      universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
      typePath sourceValue) := by
  intro newType
  show (strengthenTyped? (Term.transp modeIsUnivalent universeLevel
      universeLevelLt sourceType.weaken targetType.weaken
      sourceTypeRaw.weaken targetTypeRaw.weaken
      (Term.weaken newType typePath)
      (Term.weaken newType sourceValue))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next sourceTypeFails =>
      exfalso
      have sourceTypeSuccess :
          sourceType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some sourceType :=
        Ty.strengthen?_weaken sourceType
      rw [sourceTypeSuccess] at sourceTypeFails
      cases sourceTypeFails
  · split
    · next targetTypeFails =>
        exfalso
        have targetTypeSuccess :
            targetType.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some targetType :=
          Ty.strengthen?_weaken targetType
        rw [targetTypeSuccess] at targetTypeFails
        cases targetTypeFails
    · split
      · next sourceRawFails =>
          exfalso
          have sourceRawSuccess :
              sourceTypeRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some sourceTypeRaw :=
            RawTerm.strengthen?_weaken sourceTypeRaw
          rw [sourceRawSuccess] at sourceRawFails
          cases sourceRawFails
      · split
        · next targetRawFails =>
            exfalso
            have targetRawSuccess :
                targetTypeRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some targetTypeRaw :=
              RawTerm.strengthen?_weaken targetTypeRaw
            rw [targetRawSuccess] at targetRawFails
            cases targetRawFails
        · split
          · next pathRecurse =>
              exfalso
              have totHyp := pathIH newType
              dsimp only [strengthenTyped?] at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType typePath))) = true :=
                pathRecurse ▸ totHyp
              cases this
          · split
            · next sourceRecurse =>
                exfalso
                have totHyp := sourceIH newType
                dsimp only [strengthenTyped?] at totHyp
                have : Option.isSome (none (α := StrengtheningResult
                    (ContextStrengthening.dropNewest context newType)
                    (Term.weaken newType sourceValue))) = true :=
                  sourceRecurse ▸ totHyp
                cases this
            · rfl

/-- 1-IH non-binder totality: `Term.uaToEquiv`.  Two Ty (leftTy,
rightTy) + two RawTerm (leftTyRaw, rightTyRaw) + one Term IH (proof). -/
theorem isTotalOnWeaken_uaToEquiv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    {proof : Term context
              (Ty.id (Ty.universe innerLevel innerLevelLt)
                     leftTyRaw rightTyRaw)
              proofRaw}
    (proofIH : IsTotalOnWeaken proof) :
    IsTotalOnWeaken (Term.uaToEquiv innerLevel innerLevelLt leftTy
      rightTy leftTyRaw rightTyRaw proof) := by
  intro newType
  show (strengthenTyped? (Term.uaToEquiv innerLevel innerLevelLt
      leftTy.weaken rightTy.weaken
      leftTyRaw.weaken rightTyRaw.weaken
      (Term.weaken newType proof))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next leftTyFails =>
      exfalso
      have leftTySuccess :
          leftTy.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some leftTy :=
        Ty.strengthen?_weaken leftTy
      rw [leftTySuccess] at leftTyFails
      cases leftTyFails
  · split
    · next rightTyFails =>
        exfalso
        have rightTySuccess :
            rightTy.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some rightTy :=
          Ty.strengthen?_weaken rightTy
        rw [rightTySuccess] at rightTyFails
        cases rightTyFails
    · split
      · next leftRawFails =>
          exfalso
          have leftRawSuccess :
              leftTyRaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some leftTyRaw :=
            RawTerm.strengthen?_weaken leftTyRaw
          rw [leftRawSuccess] at leftRawFails
          cases leftRawFails
      · split
        · next rightRawFails =>
            exfalso
            have rightRawSuccess :
                rightTyRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some rightTyRaw :=
              RawTerm.strengthen?_weaken rightTyRaw
            rw [rightRawSuccess] at rightRawFails
            cases rightRawFails
        · split
          · next proofRecurse =>
              exfalso
              have totHyp := proofIH newType
              dsimp only [strengthenTyped?] at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType proof))) = true :=
                proofRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.pathApp`.  One Ty (carrierType)
+ two RawTerm (leftEndpoint, rightEndpoint) + two Term IH (pathTerm,
intervalTerm). -/
theorem isTotalOnWeaken_pathApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm : Term context
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term context Ty.interval intervalRaw}
    (pathIH : IsTotalOnWeaken pathTerm)
    (intervalIH : IsTotalOnWeaken intervalTerm) :
    IsTotalOnWeaken (Term.pathApp modeIsUnivalent pathTerm
      intervalTerm) := by
  intro newType
  show (strengthenTyped? (Term.pathApp modeIsUnivalent
      (Term.weaken newType pathTerm)
      (Term.weaken newType intervalTerm))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrierType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierType :=
        Ty.strengthen?_weaken carrierType
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next pathRecurse =>
            exfalso
            have totHyp := pathIH newType
            dsimp only [strengthenTyped?] at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType pathTerm))) = true :=
              pathRecurse ▸ totHyp
            cases this
        · split
          · next intervalRecurse =>
              exfalso
              have totHyp := intervalIH newType
              dsimp only [strengthenTyped?] at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType intervalTerm))) = true :=
                intervalRecurse ▸ totHyp
              cases this
          · rfl

/-- 2-IH non-binder totality: `Term.hcompPath`.  One Ty (carrierType)
+ two RawTerm (leftEndpoint, rightEndpoint) + two Term IH (sidesPath,
capValue). -/
theorem isTotalOnWeaken_hcompPath {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    (leftEndpoint rightEndpoint : RawTerm scope)
    {sidesPathRaw capRaw : RawTerm scope}
    {sidesPath :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIH : IsTotalOnWeaken sidesPath)
    (capIH : IsTotalOnWeaken capValue) :
    IsTotalOnWeaken (Term.hcompPath modeIsUnivalent leftEndpoint
      rightEndpoint sidesPath capValue) := by
  intro newType
  show (strengthenTyped? (Term.hcompPath modeIsUnivalent
      leftEndpoint.weaken rightEndpoint.weaken
      (Term.weaken newType sidesPath)
      (Term.weaken newType capValue))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierFails =>
      exfalso
      have carrierSuccess :
          carrierType.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierType :=
        Ty.strengthen?_weaken carrierType
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · split
    · next leftFails =>
        exfalso
        have leftSuccess :
            leftEndpoint.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some leftEndpoint :=
          RawTerm.strengthen?_weaken leftEndpoint
        rw [leftSuccess] at leftFails
        cases leftFails
    · split
      · next rightFails =>
          exfalso
          have rightSuccess :
              rightEndpoint.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some rightEndpoint :=
            RawTerm.strengthen?_weaken rightEndpoint
          rw [rightSuccess] at rightFails
          cases rightFails
      · split
        · next sidesRecurse =>
            exfalso
            have totHyp := sidesIH newType
            dsimp only [strengthenTyped?] at totHyp
            have : Option.isSome (none (α := StrengtheningResult
                (ContextStrengthening.dropNewest context newType)
                (Term.weaken newType sidesPath))) = true :=
              sidesRecurse ▸ totHyp
            cases this
        · split
          · next capRecurse =>
              exfalso
              have totHyp := capIH newType
              dsimp only [strengthenTyped?] at totHyp
              have : Option.isSome (none (α := StrengtheningResult
                  (ContextStrengthening.dropNewest context newType)
                  (Term.weaken newType capValue))) = true :=
                capRecurse ▸ totHyp
              cases this
          · rfl

/-- 1-IH non-binder totality: `Term.uaIntroHet`.  Two implicit Ty
(carrierA, carrierB) + two RawTerm (carrierARaw, carrierBRaw) +
one Term IH (equivWitness).  Dispatcher chains 6 successes (2 Ty
implicit + 4 RawTerm) before the IH split. -/
theorem isTotalOnWeaken_uaIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    {equivWitness : Term context (Ty.equiv carrierA carrierB)
      (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivIH : IsTotalOnWeaken equivWitness) :
    IsTotalOnWeaken (Term.uaIntroHet innerLevel innerLevelLt
      carrierARaw carrierBRaw equivWitness) := by
  intro newType
  show (strengthenTyped? (Term.uaIntroHet innerLevel innerLevelLt
      carrierARaw.weaken carrierBRaw.weaken
      (Term.weaken newType equivWitness))).isSome
  dsimp only [strengthenTyped?]
  dsimp only [partialStrengthenTyped?]
  split
  · next carrierAFails =>
      exfalso
      have carrierASuccess :
          carrierA.weaken.partialStrengthen?
              (ContextStrengthening.dropNewest context newType).back =
            some carrierA :=
        Ty.strengthen?_weaken carrierA
      rw [carrierASuccess] at carrierAFails
      cases carrierAFails
  · split
    · next carrierBFails =>
        exfalso
        have carrierBSuccess :
            carrierB.weaken.partialStrengthen?
                (ContextStrengthening.dropNewest context newType).back =
              some carrierB :=
          Ty.strengthen?_weaken carrierB
        rw [carrierBSuccess] at carrierBFails
        cases carrierBFails
    · split
      · next carrierARawFails =>
          exfalso
          have carrierARawSuccess :
              carrierARaw.weaken.partialStrengthen?
                  (ContextStrengthening.dropNewest context newType).back =
                some carrierARaw :=
            RawTerm.strengthen?_weaken carrierARaw
          rw [carrierARawSuccess] at carrierARawFails
          cases carrierARawFails
      · split
        · next carrierBRawFails =>
            exfalso
            have carrierBRawSuccess :
                carrierBRaw.weaken.partialStrengthen?
                    (ContextStrengthening.dropNewest context newType).back =
                  some carrierBRaw :=
              RawTerm.strengthen?_weaken carrierBRaw
            rw [carrierBRawSuccess] at carrierBRawFails
            cases carrierBRawFails
        · split
          · next forwardRawFails =>
              exfalso
              have forwardRawSuccess :
                  forwardRaw.weaken.partialStrengthen?
                      (ContextStrengthening.dropNewest context newType).back =
                    some forwardRaw :=
                RawTerm.strengthen?_weaken forwardRaw
              rw [forwardRawSuccess] at forwardRawFails
              cases forwardRawFails
          · split
            · next backwardRawFails =>
                exfalso
                have backwardRawSuccess :
                    backwardRaw.weaken.partialStrengthen?
                        (ContextStrengthening.dropNewest context newType).back =
                      some backwardRaw :=
                  RawTerm.strengthen?_weaken backwardRaw
                rw [backwardRawSuccess] at backwardRawFails
                cases backwardRawFails
            · split
              · next equivRecurse =>
                  exfalso
                  have totHyp := equivIH newType
                  dsimp only [strengthenTyped?] at totHyp
                  have : Option.isSome (none (α := StrengtheningResult
                      (ContextStrengthening.dropNewest context newType)
                      (Term.weaken newType equivWitness))) = true :=
                    equivRecurse ▸ totHyp
                  cases this
              · rfl

end Term

end LeanFX2
